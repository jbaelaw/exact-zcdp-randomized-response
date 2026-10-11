import ExactZCDP.ShapeBounds

/-! Global shape of the exact randomized-response objective. -/

namespace ExactZCDP

open Set Filter
open scoped Topology

noncomputable section

variable {a c x y : ℝ}

@[simp] theorem F_at_base (a c : ℝ) : F a c a = 0 := by simp [F]

private theorem F_deriv_pos (ha : 0 < a) (hc : 0 ≤ c) (hx : a < x)
    (hg : 0 < g c x) : 0 < deriv (F a c) x := by
  have hxpos : 0 < x := ha.trans hx
  rw [(hasDerivAt_F (a := a) hc (lt_trans ha hx)).deriv]
  have hs : 0 < x ^ 2 - a ^ 2 := sq_sub_sq_pos ha hx
  exact div_pos (mul_pos hs hg) (by have := denom_pos hc x; positivity)

private theorem F_deriv_neg (ha : 0 < a) (hc : 0 ≤ c) (hx : a < x)
    (hg : g c x < 0) : deriv (F a c) x < 0 := by
  have hxpos : 0 < x := ha.trans hx
  rw [(hasDerivAt_F (a := a) hc (lt_trans ha hx)).deriv]
  have hs : 0 < x ^ 2 - a ^ 2 := sq_sub_sq_pos ha hx
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hs hg)
    (by have := denom_pos hc x; positivity)

private theorem Q_deriv_pos (ha : 0 < a) (hc : 0 ≤ c) (hx : a < x)
    (hF : 0 < F a c x) : 0 < deriv (Q a c) x := by
  have hxpos : 0 < x := ha.trans hx
  rw [(hasDerivAt_Q hc ha hx).deriv]
  have hs : 0 < x ^ 2 - a ^ 2 := sq_sub_sq_pos ha hx
  exact div_pos (by positivity) (sq_pos_of_pos hs)

private theorem Q_deriv_neg (ha : 0 < a) (hc : 0 ≤ c) (hx : a < x)
    (hF : F a c x < 0) : deriv (Q a c) x < 0 := by
  have hxpos : 0 < x := ha.trans hx
  rw [(hasDerivAt_Q hc ha hx).deriv]
  have hs : 0 < x ^ 2 - a ^ 2 := sq_sub_sq_pos ha hx
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hF)
    (sq_pos_of_pos hs)

/-- Endpoint curvature, including equality, forces strict decrease of `F`. -/
theorem endpoint_F_strictAnti (ha : 0 < a) (hc : 0 ≤ c) (hg : g c a ≤ 0) :
    StrictAntiOn (F a c) (Ici a) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici a)
  · exact (continuousOn_F hc).mono (fun z hz => lt_of_lt_of_le ha hz)
  · intro z hz
    rw [interior_Ici] at hz
    exact F_deriv_neg ha hc hz (g_nonpos_persists_strict hc ha hz hg)

/-- `F` is strictly negative to the right of an endpoint with nonpositive curvature. -/
theorem endpoint_F_neg (ha : 0 < a) (hc : 0 ≤ c) (hg : g c a ≤ 0)
    (hx : a < x) : F a c x < 0 := by
  simpa using endpoint_F_strictAnti ha hc hg (le_refl a) (le_of_lt hx) hx

/-- The quotient is strictly decreasing throughout the endpoint regime. -/
theorem endpoint_Q_strictAnti (ha : 0 < a) (hc : 0 ≤ c) (hg : g c a ≤ 0) :
    StrictAntiOn (Q a c) (Ioi a) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi a) (continuousOn_Q hc ha)
  intro z hz
  rw [interior_Ioi] at hz
  exact Q_deriv_neg ha hc hz (endpoint_F_neg ha hc hg hz)

/-- The limiting derivative is exactly the least uniform upper bound in the endpoint regime. -/
theorem endpoint_Q_bound_iff (ha : 0 < a) (hc : 0 ≤ c) (hg : g c a ≤ 0) (r : ℝ) :
    (∀ x, a < x → Q a c x ≤ r) ↔ d c a ≤ r := by
  constructor
  · intro hr
    exact le_of_tendsto (tendsto_Q_right ha hc)
      (Filter.eventually_of_mem self_mem_nhdsWithin (fun z hz => hr z hz))
  · intro hr z hz
    have hbound : Q a c z ≤ d c a := by
      apply ge_of_tendsto (tendsto_Q_right ha hc)
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hz).filter_mono nhdsWithin_le_nhds] with w hw hwz
      exact le_of_lt (endpoint_Q_strictAnti ha hc hg hw hz hwz)
    exact le_trans hbound hr

/-- Complete shape information for the unique interior optimizer. -/
structure InteriorShape (a c x : ℝ) : Prop where
  lower : a < x
  upper : x < U a c
  root : F a c x = 0
  unique_root : ∀ y, a < y → F a c y = 0 → y = x
  positive : ∀ y, a < y → y < x → 0 < F a c y
  negative : ∀ y, x < y → F a c y < 0
  mono : StrictMonoOn (Q a c) (Ioc a x)
  anti : StrictAntiOn (Q a c) (Ici x)
  value : Q a c x = d c x
  is_max : ∀ y, a < y → Q a c y ≤ Q a c x
  unique_max : ∀ y, a < y → Q a c y = Q a c x → y = x

/-- The root equation identifies the maximum value with the derivative. -/
theorem Q_eq_d_of_F_eq_zero (ha : 0 < a) (hx : a < x) (hF : F a c x = 0) :
    Q a c x = d c x := by
  have hs : x ^ 2 - a ^ 2 ≠ 0 := ne_of_gt (sq_sub_sq_pos ha hx)
  apply (div_eq_iff hs).2
  dsimp [F] at hF
  nlinarith

/-- The interior regime can occur only above the curvature parameter `2`. -/
theorem c_gt_two_of_g_pos (ha : 0 < a) (hg : 0 < g c a) : 2 < c := by
  by_contra h
  have := g_neg_of_c_le_two (le_of_not_gt h) ha
  linarith

/-- Positive endpoint curvature has exactly one later zero of the auxiliary function. -/
theorem interior_shape (ha : 0 < a) (hc : 0 ≤ c) (hg : 0 < g c a) :
    ∃ x, InteriorShape a c x := by
  have hU : a < U a c := U_gt ha hc
  have hFU : F a c (U a c) < 0 := F_U_neg ha hc
  have hcontF : ContinuousOn (F a c) (Icc a (U a c)) :=
    (continuousOn_F hc).mono (fun z hz => lt_of_lt_of_le ha hz.1)
  obtain ⟨v, hv, hdv⟩ := exists_hasDerivAt_eq_slope (F a c)
    (fun z => (z ^ 2 - a ^ 2) * g c z / (2 * z ^ 2 * (c + Real.cosh z) ^ 2))
    hU hcontF (fun z hz => hasDerivAt_F hc (lt_trans ha hz.1))
  have hvpos : 0 < v := lt_trans ha hv.1
  have hgv : g c v < 0 := by
    have hdn : (v ^ 2 - a ^ 2) * g c v / (2 * v ^ 2 * (c + Real.cosh v) ^ 2) < 0 := by
      rw [hdv, F_at_base, sub_zero]
      exact div_neg_of_neg_of_pos hFU (sub_pos.mpr hU)
    have hden : 0 < 2 * v ^ 2 * (c + Real.cosh v) ^ 2 := by
      have := denom_pos hc v
      positivity
    have hn : (v ^ 2 - a ^ 2) * g c v < 0 := by
      simpa using (div_lt_iff₀ hden).mp hdn
    have hs : 0 < v ^ 2 - a ^ 2 := sq_sub_sq_pos ha hv.1
    by_contra hnon
    have := mul_nonneg hs.le (le_of_not_gt hnon)
    linarith
  obtain ⟨b, hb, hgb⟩ := intermediate_value_Icc' (le_of_lt hv.1)
    (continuous_g c).continuousOn ⟨le_of_lt hgv, le_of_lt hg⟩
  have hab : a < b := by
    have hne : a ≠ b := by intro he; subst b; linarith
    exact lt_of_le_of_ne hb.1 hne
  have hbv : b < v := by
    have hne : b ≠ v := by intro he; subst b; linarith
    exact lt_of_le_of_ne hb.2 hne
  have hbU : b < U a c := lt_trans hbv hv.2
  have hbpos : 0 < b := lt_trans ha hab
  have gpos : ∀ z, a < z → z < b → 0 < g c z := by
    intro z haz hzb
    by_contra h
    have := g_nonpos_persists_strict hc (lt_trans ha haz) hzb (le_of_not_gt h)
    linarith
  have gneg : ∀ z, b < z → g c z < 0 := by
    intro z hbz
    exact g_nonpos_persists_strict hc hbpos hbz (le_of_eq hgb)
  have Fmono : StrictMonoOn (F a c) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b)
    · exact (continuousOn_F hc).mono (fun z hz => lt_of_lt_of_le ha hz.1)
    · intro z hz
      rw [interior_Icc] at hz
      exact F_deriv_pos ha hc hz.1 (gpos z hz.1 hz.2)
  have Fanti : StrictAntiOn (F a c) (Ici b) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici b)
    · exact (continuousOn_F hc).mono (fun z hz => lt_of_lt_of_le hbpos hz)
    · intro z hz
      rw [interior_Ici] at hz
      exact F_deriv_neg ha hc (lt_trans hab hz) (gneg z hz)
  have hFb : 0 < F a c b := by
    simpa using Fmono ⟨le_refl a, le_of_lt hab⟩ ⟨le_of_lt hab, le_refl b⟩ hab
  obtain ⟨x, hx, hFx⟩ := intermediate_value_Icc' (le_of_lt hbU)
    ((continuousOn_F hc).mono (fun z hz => lt_of_lt_of_le hbpos hz.1))
    ⟨le_of_lt hFU, le_of_lt hFb⟩
  have hbx : b < x := by
    have hne : b ≠ x := by intro he; subst x; linarith
    exact lt_of_le_of_ne hx.1 hne
  have hxU : x < U a c := by
    have hne : x ≠ U a c := by intro he; subst x; linarith
    exact lt_of_le_of_ne hx.2 hne
  have hax : a < x := lt_trans hab hbx
  have Fpos : ∀ y, a < y → y < x → 0 < F a c y := by
    intro y hay hyx
    by_cases hyb : y ≤ b
    · simpa using Fmono ⟨le_refl a, le_of_lt hab⟩ ⟨le_of_lt hay, hyb⟩ hay
    · have hby : b ≤ y := le_of_lt (lt_of_not_ge hyb)
      have := Fanti hby (le_of_lt hbx) hyx
      linarith
  have Fneg : ∀ y, x < y → F a c y < 0 := by
    intro y hxy
    have := Fanti (le_of_lt hbx) (le_of_lt (lt_trans hbx hxy)) hxy
    linarith
  have Qmono : StrictMonoOn (Q a c) (Ioc a x) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc a x)
    · exact (continuousOn_Q hc ha).mono (fun z hz => hz.1)
    · intro z hz
      rw [interior_Ioc] at hz
      exact Q_deriv_pos ha hc hz.1 (Fpos z hz.1 hz.2)
  have Qanti : StrictAntiOn (Q a c) (Ici x) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici x)
    · exact (continuousOn_Q hc ha).mono (fun z hz => lt_of_lt_of_le hax hz)
    · intro z hz
      rw [interior_Ici] at hz
      exact Q_deriv_neg ha hc (lt_trans hax hz) (Fneg z hz)
  refine ⟨x, ⟨hax, hxU, hFx, ?_, Fpos, Fneg, Qmono, Qanti,
    Q_eq_d_of_F_eq_zero ha hax hFx, ?_, ?_⟩⟩
  · intro y hay hFy
    rcases lt_trichotomy y x with hyx | hEq | hxy
    · have := Fpos y hay hyx; linarith
    · exact hEq
    · have := Fneg y hxy; linarith
  · intro y hay
    rcases le_total y x with hyx | hxy
    · exact Qmono.monotoneOn ⟨hay, hyx⟩ ⟨hax, le_refl x⟩ hyx
    · exact Qanti.antitoneOn (le_refl x) hxy hxy
  · intro y hay hQ
    rcases lt_trichotomy y x with hyx | hEq | hxy
    · have := Qmono ⟨hay, le_of_lt hyx⟩ ⟨hax, le_refl x⟩ hyx; linarith
    · exact hEq
    · have := Qanti (le_refl x) (le_of_lt hxy) hxy; linarith

/-- In the interior regime the unique attained value is the least uniform upper bound. -/
theorem interior_Q_bound_iff (hs : InteriorShape a c x) (r : ℝ) :
    (∀ y, a < y → Q a c y ≤ r) ↔ d c x ≤ r := by
  constructor
  · intro hr
    rw [← hs.value]
    exact hr x hs.lower
  · intro hr y hy
    exact le_trans (hs.is_max y hy) (by simpa [hs.value] using hr)

/-- An interior optimizer strictly improves on the limiting endpoint value. -/
theorem interior_endpoint_lt (ha : 0 < a) (hc : 0 ≤ c) (hs : InteriorShape a c x) :
    d c a < d c x := by
  obtain ⟨y, hay, hyx⟩ := exists_between hs.lower
  have hlim : d c a ≤ Q a c y := by
    apply le_of_tendsto (tendsto_Q_right ha hc)
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hay).filter_mono nhdsWithin_le_nhds] with w hw hwy
    exact (hs.mono ⟨hw, (lt_trans hwy hyx).le⟩ ⟨hay, hyx.le⟩ hwy).le
  have hstrict := hs.mono ⟨hay, hyx.le⟩ ⟨hs.lower, le_refl x⟩ hyx
  rw [hs.value] at hstrict
  exact hlim.trans_lt hstrict

end
end ExactZCDP
