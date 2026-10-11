import ExactZCDP.Base

namespace ExactZCDP
noncomputable section
open Set
variable {a c x y : ℝ}

lemma denom_pos (hc : 0 ≤ c) (x : ℝ) : 0 < c + Real.cosh x :=
  add_pos_of_nonneg_of_pos hc (Real.cosh_pos x)

lemma hasDerivAt_h (hc : 0 ≤ c) (x : ℝ) : HasDerivAt (h c) (hp c x) x := by
  change HasDerivAt (fun y : ℝ => Real.log (c + Real.cosh y)) _ x
  exact ((Real.hasDerivAt_cosh x).const_add c).log (ne_of_gt (denom_pos hc x))

lemma hasDerivAt_hp (hc : 0 ≤ c) (x : ℝ) :
    HasDerivAt (hp c) ((1 + c * Real.cosh x) / (c + Real.cosh x) ^ 2) x := by
  convert (Real.hasDerivAt_sinh x).div ((Real.hasDerivAt_cosh x).const_add c)
    (ne_of_gt (denom_pos hc x)) using 1 <;> try rfl
  congr 1
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

lemma hasDerivAt_g (c x : ℝ) :
    HasDerivAt (g c) (Real.sinh x * (c * x - 2 * Real.sinh x)) x := by
  have hd := ((hasDerivAt_id x).mul (((Real.hasDerivAt_cosh x).const_mul c).const_add 1)).sub
    ((Real.hasDerivAt_sinh x).mul ((Real.hasDerivAt_cosh x).const_add c))
  convert hd using 1 <;> try rfl
  dsimp
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

lemma hasDerivAt_d (hc : 0 ≤ c) (hx : 0 < x) :
    HasDerivAt (d c) (g c x / (2 * x ^ 2 * (c + Real.cosh x) ^ 2)) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hden : c + Real.cosh x ≠ 0 := ne_of_gt (denom_pos hc x)
  have hd := (Real.hasDerivAt_sinh x).div
    (((hasDerivAt_id x).const_mul 2).mul ((Real.hasDerivAt_cosh x).const_add c))
    (by positivity : 2 * x * (c + Real.cosh x) ≠ 0)
  convert hd using 1 <;> try rfl
  dsimp [g]
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

lemma hasDerivAt_F (hc : 0 ≤ c) (hx : 0 < x) :
    HasDerivAt (F a c)
      ((x ^ 2 - a ^ 2) * g c x / (2 * x ^ 2 * (c + Real.cosh x) ^ 2)) x := by
  have hd := ((((hasDerivAt_id x).pow 2).sub_const (a ^ 2)).mul (hasDerivAt_d hc hx)).sub
    (hasDerivAt_h hc x)
  have hd' := hd.add_const (h c a)
  convert hd' using 1 <;> try rfl
  dsimp [hp, d]
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hden : c + Real.cosh x ≠ 0 := ne_of_gt (denom_pos hc x)
  field_simp
  ring

lemma sq_sub_sq_pos (ha : 0 < a) (hx : a < x) : 0 < x ^ 2 - a ^ 2 := by
  nlinarith

lemma hasDerivAt_Q (hc : 0 ≤ c) (ha : 0 < a) (hx : a < x) :
    HasDerivAt (Q a c) (2 * x * F a c x / (x ^ 2 - a ^ 2) ^ 2) x := by
  have hd := ((hasDerivAt_h hc x).sub_const (h c a)).div
    (((hasDerivAt_id x).pow 2).sub_const (a ^ 2)) (ne_of_gt (sq_sub_sq_pos ha hx))
  convert hd using 1 <;> try rfl
  congr 1
  dsimp [F, d, hp]
  have hx0 : x ≠ 0 := ne_of_gt (ha.trans hx)
  have hden : c + Real.cosh x ≠ 0 := ne_of_gt (denom_pos hc x)
  field_simp
  ring

lemma continuous_h (hc : 0 ≤ c) : Continuous (h c) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_h hc x).continuousAt
lemma continuous_hp (hc : 0 ≤ c) : Continuous (hp c) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_hp hc x).continuousAt
lemma continuous_g (c : ℝ) : Continuous (g c) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_g c x).continuousAt
lemma continuousOn_d (hc : 0 ≤ c) : ContinuousOn (d c) (Ioi 0) :=
  fun _ hx => (hasDerivAt_d hc hx).continuousAt.continuousWithinAt
lemma continuousOn_F (hc : 0 ≤ c) : ContinuousOn (F a c) (Ioi 0) :=
  fun _ hx => (hasDerivAt_F hc hx).continuousAt.continuousWithinAt
lemma continuousOn_Q (hc : 0 ≤ c) (ha : 0 < a) : ContinuousOn (Q a c) (Ioi a) :=
  fun _ hx => (hasDerivAt_Q hc ha hx).continuousAt.continuousWithinAt

lemma hp_nonneg (hc : 0 ≤ c) (hx : 0 ≤ x) : 0 ≤ hp c x := by
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (denom_pos hc x).le
lemma hp_le_one (hc : 0 ≤ c) (x : ℝ) : hp c x ≤ 1 := by
  apply (div_le_one (denom_pos hc x)).mpr
  linarith [Real.sinh_lt_cosh (x := x)]
lemma hp_deriv_nonneg (hc : 0 ≤ c) (x : ℝ) :
    0 ≤ (1 + c * Real.cosh x) / (c + Real.cosh x) ^ 2 := by positivity
lemma hp_deriv_le_one (hc : 0 ≤ c) (x : ℝ) :
    (1 + c * Real.cosh x) / (c + Real.cosh x) ^ 2 ≤ 1 := by
  apply (div_le_one (sq_pos_of_pos (denom_pos hc x))).mpr
  have hcosh := Real.one_le_cosh x
  have hmul : 0 ≤ c * Real.cosh x := mul_nonneg hc (Real.cosh_pos x).le
  nlinarith [sq_nonneg c, sq_nonneg (Real.sinh x), Real.cosh_sq_sub_sinh_sq x]
lemma monotone_hp (hc : 0 ≤ c) : Monotone (hp c) := by
  apply monotone_of_deriv_nonneg (fun x => (hasDerivAt_hp hc x).differentiableAt)
  intro x
  rw [(hasDerivAt_hp hc x).deriv]
  exact hp_deriv_nonneg hc x

lemma hasDerivAt_x_cosh_sub_sinh (x : ℝ) :
    HasDerivAt (fun x : ℝ => x * Real.cosh x - Real.sinh x) (x * Real.sinh x) x := by
  convert ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub
    (Real.hasDerivAt_sinh x) using 1
  · rfl
  · dsimp; ring
lemma x_cosh_sub_sinh_pos (hx : 0 < x) :
    0 < x * Real.cosh x - Real.sinh x := by
  have hm : StrictMonoOn (fun x : ℝ => x * Real.cosh x - Real.sinh x) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact (continuous_id.mul Real.continuous_cosh |>.sub Real.continuous_sinh).continuousOn
    · intro y hy
      rw [interior_Ici, mem_Ioi] at hy
      rw [(hasDerivAt_x_cosh_sub_sinh y).deriv]
      exact mul_pos hy (Real.sinh_pos_iff.mpr hy)
  simpa using hm (show (0 : ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 from hx.le) hx
lemma strictMonoOn_sinh_div : StrictMonoOn (fun x : ℝ => Real.sinh x / x) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · exact Real.continuous_sinh.continuousOn.div continuousOn_id (fun x hx => ne_of_gt hx)
  · intro x hx
    rw [interior_Ioi, mem_Ioi] at hx
    have hd : HasDerivAt (fun t : ℝ => Real.sinh t / t)
        ((Real.cosh x * x - Real.sinh x) / x ^ 2) x := by
      convert (Real.hasDerivAt_sinh x).fun_div (hasDerivAt_id x) (ne_of_gt hx) using 1 <;> simp
    rw [hd.deriv]
    apply div_pos _ (sq_pos_of_pos hx)
    simpa [mul_comm] using x_cosh_sub_sinh_pos hx

lemma hp_sub_le_sub (hc : 0 ≤ c) (hxy : x ≤ y) : hp c y - hp c x ≤ y - x := by
  have hh := image_sub_le_mul_sub_of_deriv_le
    (fun z => (hasDerivAt_hp hc z).differentiableAt)
    (fun z => by rw [(hasDerivAt_hp hc z).deriv]; exact hp_deriv_le_one hc z) hxy
  simpa using hh

@[simp] lemma g_zero (c : ℝ) : g c 0 = 0 := by simp [g]

lemma g_deriv_neg_of_nonpos (hx : 0 < x) (hxy : x < y) (hg : g c x ≤ 0) :
    deriv (g c) y < 0 := by
  obtain ⟨z, hz, heq⟩ := exists_deriv_eq_slope (g c) hx
    (continuous_g c).continuousOn
    (fun t _ => (hasDerivAt_g c t).differentiableAt.differentiableWithinAt)
  have hdz : deriv (g c) z ≤ 0 := by
    rw [heq, g_zero, sub_zero, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg hg hx.le
  rw [(hasDerivAt_g c z).deriv] at hdz
  have hcz : c * z ≤ 2 * Real.sinh z := by
    by_contra hcz
    have hpos := mul_pos (Real.sinh_pos_iff.mpr hz.1) (sub_pos.mpr (lt_of_not_ge hcz))
    linarith
  have hcle : c ≤ 2 * (Real.sinh z / z) := by
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hz.1).mpr hcz
  have hy : 0 < y := hx.trans hxy
  have hquot := strictMonoOn_sinh_div hz.1 hy (hz.2.trans hxy)
  have hclt : c < 2 * (Real.sinh y / y) :=
    hcle.trans_lt (mul_lt_mul_of_pos_left hquot (by norm_num))
  have hcy : c * y < 2 * Real.sinh y := by
    apply (lt_div_iff₀ hy).mp
    simpa [mul_div_assoc] using hclt
  rw [(hasDerivAt_g c y).deriv]
  exact mul_neg_of_pos_of_neg (Real.sinh_pos_iff.mpr hy) (sub_neg.mpr hcy)

lemma g_nonpos_persists_strict (_hc : 0 ≤ c) (hx : 0 < x) (hxy : x < y)
    (hg : g c x ≤ 0) : g c y < 0 := by
  have hm : StrictAntiOn (g c) (Ici x) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici x) (continuous_g c).continuousOn
    intro z hz
    rw [interior_Ici, mem_Ioi] at hz
    exact g_deriv_neg_of_nonpos hx hz hg
  exact (hm (le_refl x) hxy.le hxy).trans_le hg

lemma g_neg_of_c_le_two (hc : c ≤ 2) (hx : 0 < x) : g c x < 0 := by
  have hm : StrictAntiOn (g c) (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0) (continuous_g c).continuousOn
    intro z hz
    rw [interior_Ici, mem_Ioi] at hz
    rw [(hasDerivAt_g c z).deriv]
    apply mul_neg_of_pos_of_neg (Real.sinh_pos_iff.mpr hz)
    have hcz := mul_le_mul_of_nonneg_right hc hz.le
    have hzs := Real.self_lt_sinh_iff.mpr hz
    linarith
  have hh := hm (show (0 : ℝ) ∈ Ici 0 by simp) (show x ∈ Ici 0 from hx.le) hx
  simpa using hh

end
end ExactZCDP
