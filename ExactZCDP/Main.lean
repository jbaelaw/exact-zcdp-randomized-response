import ExactZCDP.Mechanism
import ExactZCDP.Parameters
import ExactZCDP.Shape
import ExactZCDP.RootEquation
import ExactZCDP.EndpointLimit

/-! The complete all-parameter characterization for the actual randomized-response mechanism. -/

namespace ExactZCDP

open Set Filter
open scoped Topology

noncomputable section

variable {k : ℕ} {ε ρ x : ℝ}

/-- Uniform profile bounds transported through the bijective change of order. -/
theorem profile_bound_iff_Q (hk : 2 ≤ k) (he : 0 < ε) (r : ℝ) :
    (∀ α, 1 < α → profile k ε α ≤ r) ↔
    ∀ y, paramA ε < y → Q (paramA ε) (paramC k ε) y ≤ r / ε ^ 2 := by
  have he2 : 0 < ε ^ 2 := sq_pos_of_pos he
  constructor
  · intro hr y hy
    have hα := (pointOrder_gt_one_iff he).2 hy
    have hq := hr (pointOrder ε y) hα
    rw [profile_eq_Q hk he hα, orderPoint_pointOrder he] at hq
    exact (le_div_iff₀ he2).2 (by simpa [mul_comm] using hq)
  · intro hr α hα
    rw [profile_eq_Q hk he hα]
    have hq := hr (orderPoint ε α) ((orderPoint_gt_paramA_iff he).2 hα)
    exact (by simpa [mul_comm] using (le_div_iff₀ he2).1 hq)

/-- In the endpoint regime the closed expression is the least zCDP parameter. -/
theorem endpoint_zCDP_iff (hk : 2 ≤ k) (he : 0 < ε) (hρ : 0 ≤ ρ)
    (hK : (k : ℝ) ≤ threshold ε) :
    IsZCDP k ε ρ ↔ endpointValue k ε ≤ ρ := by
  rw [isZCDP_iff_profile hk ε ρ hρ, profile_bound_iff_Q hk he ρ,
    endpoint_Q_bound_iff (paramA_pos he) (paramC_nonneg hk ε)
      ((g_param_nonpos_iff he).2 hK)]
  rw [le_div_iff₀ (sq_pos_of_pos he)]
  rw [mul_comm, endpoint_identity hk he]

/-- The profile strictly decreases even when the threshold holds with equality. -/
theorem endpoint_profile_strictAnti (hk : 2 ≤ k) (he : 0 < ε)
    (hK : (k : ℝ) ≤ threshold ε) : StrictAntiOn (profile k ε) (Ioi 1) := by
  intro α hα β hβ hαβ
  rw [profile_eq_Q hk he hβ, profile_eq_Q hk he hα]
  apply mul_lt_mul_of_pos_left _ (sq_pos_of_pos he)
  apply endpoint_Q_strictAnti (paramA_pos he) (paramC_nonneg hk ε)
    ((g_param_nonpos_iff he).2 hK)
    ((orderPoint_gt_paramA_iff he).2 hα) ((orderPoint_gt_paramA_iff he).2 hβ)
  dsimp [orderPoint]
  exact mul_lt_mul_of_pos_left (sub_lt_sub_right hαβ _) he

/-- Every interior root has exactly the closed optimum stated in the manuscript. -/
theorem interior_zCDP_iff (hk : 2 ≤ k) (he : 0 < ε) (hρ : 0 ≤ ρ)
    (hs : InteriorShape (paramA ε) (paramC k ε) x) :
    IsZCDP k ε ρ ↔ ε ^ 2 * d (paramC k ε) x ≤ ρ := by
  rw [isZCDP_iff_profile hk ε ρ hρ, profile_bound_iff_Q hk he ρ,
    interior_Q_bound_iff hs, le_div_iff₀ (sq_pos_of_pos he)]
  rw [mul_comm]

/-- The equation has one and only one solution in the admissible domain. -/
theorem interior_unique_root (hk : 2 ≤ k) (he : 0 < ε)
    (hK : threshold ε < (k : ℝ)) :
    ∃! y, paramA ε < y ∧ RootEquation (paramA ε) (paramC k ε) y := by
  obtain ⟨y, hs⟩ := interior_shape (paramA_pos he) (paramC_nonneg hk ε)
    ((g_param_pos_iff he).2 hK)
  refine ⟨y, ⟨hs.lower, ?_⟩, ?_⟩
  · exact (F_eq_zero_iff_rootEquation (paramC_nonneg hk ε)
      (lt_trans (paramA_pos he) hs.lower)).1 hs.root
  · intro z hz
    exact hs.unique_root z hz.1
      ((F_eq_zero_iff_rootEquation (paramC_nonneg hk ε)
        (lt_trans (paramA_pos he) hz.1)).2 hz.2)

/-- Complete order-space information associated with an interior optimizer. -/
theorem interior_profile_maximum (hk : 2 ≤ k) (he : 0 < ε)
    (hs : InteriorShape (paramA ε) (paramC k ε) x) :
    1 < pointOrder ε x ∧
    profile k ε (pointOrder ε x) = ε ^ 2 * d (paramC k ε) x ∧
    (∀ α, 1 < α → profile k ε α ≤ profile k ε (pointOrder ε x)) ∧
    (∀ α, 1 < α → profile k ε α = profile k ε (pointOrder ε x) →
      α = pointOrder ε x) := by
  have ho : 1 < pointOrder ε x := (pointOrder_gt_one_iff he).2 hs.lower
  refine ⟨ho, ?_, ?_, ?_⟩
  · rw [profile_eq_Q hk he ho, orderPoint_pointOrder he, hs.value]
  · intro α hα
    rw [profile_eq_Q hk he hα, profile_eq_Q hk he ho, orderPoint_pointOrder he]
    exact mul_le_mul_of_nonneg_left
      (hs.is_max _ ((orderPoint_gt_paramA_iff he).2 hα)) (sq_nonneg ε)
  · intro α hα hv
    rw [profile_eq_Q hk he hα, profile_eq_Q hk he ho, orderPoint_pointOrder he] at hv
    have hq := (mul_left_cancel₀ (ne_of_gt (sq_pos_of_pos he)) hv)
    have hx := hs.unique_max _ ((orderPoint_gt_paramA_iff he).2 hα) hq
    rw [← pointOrder_orderPoint he α, hx]

/-- A total choice function; its optimizer property is established below in its valid regime. -/
def interiorPoint (a c : ℝ) : ℝ := Classical.epsilon (fun y => InteriorShape a c y)

theorem interiorPoint_spec {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hg : 0 < g c a) :
    InteriorShape a c (interiorPoint a c) :=
  Classical.epsilon_spec (interior_shape ha hc hg)

/-- The exact parameter, including the uniform mechanism at zero privacy parameter. -/
def exactParameter (k : ℕ) (ε : ℝ) : ℝ :=
  if ε = 0 then 0 else if (k : ℝ) ≤ threshold ε then endpointValue k ε
  else ε ^ 2 * d (paramC k ε) (interiorPoint (paramA ε) (paramC k ε))

@[simp] theorem exactParameter_zero (k : ℕ) : exactParameter k 0 = 0 := by
  simp [exactParameter]

/-- Main least-parameter theorem: all k≥2, all ε≥0, all admissible ρ. -/
theorem isZCDP_iff_exact (hk : 2 ≤ k) (he : 0 ≤ ε) (hρ : 0 ≤ ρ) :
    IsZCDP k ε ρ ↔ exactParameter k ε ≤ ρ := by
  by_cases he0 : ε = 0
  · subst ε
    simpa using isZCDP_zero_iff hk ρ
  · have hep : 0 < ε := lt_of_le_of_ne he (Ne.symm he0)
    by_cases hK : (k : ℝ) ≤ threshold ε
    · simpa [exactParameter, he0, hK] using endpoint_zCDP_iff hk hep hρ hK
    · have hg := (g_param_pos_iff hep).2 (lt_of_not_ge hK)
      have hs := interiorPoint_spec (paramA_pos hep) (paramC_nonneg hk ε) hg
      simpa [exactParameter, he0, hK] using interior_zCDP_iff hk hep hρ hs

/-- The characterized value itself is an admissible nonnegative privacy parameter. -/
theorem exactParameter_nonneg (hk : 2 ≤ k) (he : 0 ≤ ε) :
    0 ≤ exactParameter k ε := by
  by_cases he0 : ε = 0
  · simp [exactParameter, he0]
  · have hep : 0 < ε := lt_of_le_of_ne he (Ne.symm he0)
    by_cases hK : (k : ℝ) ≤ threshold ε
    · rw [exactParameter, ite_eq_right he0, ite_eq_left hK, ← endpoint_identity hk hep]
      exact mul_nonneg (sq_nonneg ε) (d_nonneg (paramC_nonneg hk ε) (paramA_pos hep))
    · rw [exactParameter, ite_eq_right he0, ite_eq_right hK]
      have hs := interiorPoint_spec (paramA_pos hep) (paramC_nonneg hk ε)
        ((g_param_pos_iff hep).2 (lt_of_not_ge hK))
      exact mul_nonneg (sq_nonneg ε) (d_nonneg (paramC_nonneg hk ε)
        (lt_trans (paramA_pos hep) hs.lower))

theorem exactParameter_isZCDP (hk : 2 ≤ k) (he : 0 ≤ ε) :
    IsZCDP k ε (exactParameter k ε) :=
  (isZCDP_iff_exact hk he (exactParameter_nonneg hk he)).2 le_rfl

/-- The threshold condition gives the stated endpoint value, including equality. -/
theorem exactParameter_endpoint (_hk : 2 ≤ k) (he : 0 < ε)
    (hK : (k : ℝ) ≤ threshold ε) :
    exactParameter k ε = endpointValue k ε := by
  simp [exactParameter, ne_of_gt he, hK]

/-- Any admissible interior root yields the same exact value. -/
theorem exactParameter_interior (hk : 2 ≤ k) (he : 0 < ε)
    (hK : threshold ε < (k : ℝ))
    (hs : InteriorShape (paramA ε) (paramC k ε) x) :
    exactParameter k ε = ε ^ 2 * d (paramC k ε) x := by
  have hsel := interiorPoint_spec (paramA_pos he) (paramC_nonneg hk ε)
    ((g_param_pos_iff he).2 hK)
  have hid := hs.unique_root _ hsel.lower hsel.root
  simp only [exactParameter, ite_eq_right (ne_of_gt he), ite_eq_right (not_le.mpr hK)]
  rw [hid]

/-- The complete interior case, in the original parameters and the printed root equation. -/
structure InteriorCharacterization (k : ℕ) (ε x : ℝ) : Prop where
  lower : paramA ε < x
  upper : x < U (paramA ε) (paramC k ε)
  bracket_formula : U (paramA ε) (paramC k ε) = 2 * Real.log (k - 1 + Real.exp ε) - ε
  equation : RootEquation (paramA ε) (paramC k ε) x
  unique_root : ∀ y, paramA ε < y → RootEquation (paramA ε) (paramC k ε) y → y = x
  exact_value : exactParameter k ε = ε ^ 2 * d (paramC k ε) x
  order_admissible : 1 < pointOrder ε x
  attained : profile k ε (pointOrder ε x) = exactParameter k ε
  maximal : ∀ α, 1 < α → profile k ε α ≤ profile k ε (pointOrder ε x)
  unique_order : ∀ α, 1 < α → profile k ε α = profile k ε (pointOrder ε x) → α = pointOrder ε x

theorem interior_characterization (hk : 2 ≤ k) (he : 0 < ε)
    (hK : threshold ε < (k : ℝ)) : ∃ y, InteriorCharacterization k ε y := by
  obtain ⟨y, hs⟩ := interior_shape (paramA_pos he) (paramC_nonneg hk ε)
    ((g_param_pos_iff he).2 hK)
  have hm := interior_profile_maximum hk he hs
  have hv := exactParameter_interior hk he hK hs
  refine ⟨y, hs.lower, hs.upper, U_parameters hk ε, ?_, ?_, hv,
    hm.1, hm.2.1.trans hv.symm, hm.2.2.1, hm.2.2.2⟩
  · exact (F_eq_zero_iff_rootEquation (paramC_nonneg hk ε)
      (lt_trans (paramA_pos he) hs.lower)).1 hs.root
  · intro z hz heq
    exact hs.unique_root z hz ((F_eq_zero_iff_rootEquation (paramC_nonneg hk ε)
      (lt_trans (paramA_pos he) hz)).2 heq)

/-- Above the threshold the interior optimum strictly improves on the endpoint limit. -/
theorem endpoint_lt_exactParameter (hk : 2 ≤ k) (he : 0 < ε)
    (hK : threshold ε < (k : ℝ)) : endpointValue k ε < exactParameter k ε := by
  have hs := interiorPoint_spec (paramA_pos he) (paramC_nonneg hk ε)
    ((g_param_pos_iff he).2 hK)
  rw [exactParameter_interior hk he hK hs, ← endpoint_identity hk he]
  exact mul_lt_mul_of_pos_left
    (interior_endpoint_lt (paramA_pos he) (paramC_nonneg hk ε) hs) (sq_pos_of_pos he)

/-- The previously necessary endpoint threshold is also sufficient, with equality included. -/
theorem endpoint_formula_iff (hk : 2 ≤ k) (he : 0 < ε) :
    exactParameter k ε = endpointValue k ε ↔ (k : ℝ) ≤ threshold ε := by
  constructor
  · intro hv
    by_contra hn
    have hh := endpoint_lt_exactParameter hk he (lt_of_not_ge hn)
    rw [hv] at hh
    exact (lt_irrefl _ hh)
  · exact exactParameter_endpoint hk he

/-- The optimum is the least element of the full set of valid zCDP parameters. -/
theorem exactParameter_isLeast (hk : 2 ≤ k) (he : 0 ≤ ε) :
    IsLeast {r : ℝ | IsZCDP k ε r} (exactParameter k ε) := by
  refine ⟨exactParameter_isZCDP hk he, ?_⟩
  intro r hr
  exact (isZCDP_iff_exact hk he hr.1).1 hr

end
end ExactZCDP
