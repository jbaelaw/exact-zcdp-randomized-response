import ExactZCDP.Shape
import ExactZCDP.Parameters
import ExactZCDP.BisectionValue

/-! Exact real-arithmetic bisection, including the exact-hit case. -/

namespace ExactZCDP

noncomputable section

/-- A root hit collapses the interval and remains an exact answer. -/
def bisectStep (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  let m := (p.1 + p.2) / 2
  if 0 < f m then (m, p.2)
  else if f m < 0 then (p.1, m)
  else (m, m)

def bisect (f : ℝ → ℝ) (a u : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, u)
  | n + 1 => bisectStep f (bisect f a u n)

/-- The sign invariant includes the root at every step. Before an exact hit,
its width is exactly halved; after a hit the two endpoints equal the root. -/
theorem bisect_invariant {f : ℝ → ℝ} {a u x : ℝ}
    (hax : a < x) (hxu : x < u) (hx : f x = 0)
    (hpos : ∀ y, a < y → y < x → 0 < f y)
    (hneg : ∀ y, x < y → f y < 0) (n : ℕ) :
    a ≤ (bisect f a u n).1 ∧ (bisect f a u n).2 ≤ u ∧
    (((bisect f a u n).1 < x ∧ x < (bisect f a u n).2 ∧
      (bisect f a u n).2 - (bisect f a u n).1 = (u - a) / (2 : ℝ) ^ n) ∨
     ((bisect f a u n).1 = x ∧ (bisect f a u n).2 = x)) := by
  induction n with
  | zero =>
    change a ≤ a ∧ u ≤ u ∧ ((a < x ∧ x < u ∧ u - a = (u - a) / (2 : ℝ) ^ 0) ∨ (a = x ∧ u = x))
    exact ⟨le_rfl, le_rfl, Or.inl ⟨hax, hxu, by simp⟩⟩
  | succ n ih =>
    rcases ih with ⟨haL, hRu, hold | hit⟩
    · rcases hold with ⟨hLx, hxR, hw⟩
      let L := (bisect f a u n).1
      let R := (bisect f a u n).2
      let m := (L + R) / 2
      have hLm : L < m := by dsimp [L, R, m]; linarith
      have hmR : m < R := by dsimp [L, R, m]; linarith
      have ham : a < m := lt_of_le_of_lt haL hLm
      have hwidth : R - L = (u - a) / (2 : ℝ) ^ n := hw
      have hhalf : (u - a) / (2 : ℝ) ^ (n + 1) = ((u - a) / (2 : ℝ) ^ n) / 2 := by
        rw [pow_succ, div_mul_eq_div_div]
      by_cases hp : 0 < f m
      · have hmx : m < x := by
          by_contra hn
          rcases (le_of_not_gt hn).eq_or_lt with he | he
          · have hm0 : f m = 0 := by rw [← he]; exact hx
            linarith
          · have := hneg m he
            linarith
        have hstep : bisect f a u (n + 1) = (m, R) := by
          change (if 0 < f m then (m, R) else if f m < 0 then (L, m) else (m, m)) = _
          rw [ite_eq_left hp]
        rw [hstep]
        refine ⟨ham.le, hRu, Or.inl ⟨hmx, hxR, ?_⟩⟩
        rw [hhalf, ← hwidth]
        dsimp [m]
        ring
      · by_cases hn : f m < 0
        · have hxm : x < m := by
            by_contra hh
            rcases (le_of_not_gt hh).lt_or_eq with he | he
            · have := hpos m ham he
              linarith
            · have hm0 : f m = 0 := by rw [he]; exact hx
              linarith
          have hstep : bisect f a u (n + 1) = (L, m) := by
            change (if 0 < f m then (m, R) else if f m < 0 then (L, m) else (m, m)) = _
            rw [ite_eq_right hp, ite_eq_left hn]
          rw [hstep]
          refine ⟨haL, (hmR.trans_le hRu).le, Or.inl ⟨hLx, hxm, ?_⟩⟩
          rw [hhalf, ← hwidth]
          dsimp [m]
          ring
        · have hmx : m = x := by
            rcases lt_trichotomy m x with hh | hh | hh
            · exact False.elim (hp (hpos m ham hh))
            · exact hh
            · exact False.elim (hn (hneg m hh))
          have hstep : bisect f a u (n + 1) = (m, m) := by
            change (if 0 < f m then (m, R) else if f m < 0 then (L, m) else (m, m)) = _
            rw [ite_eq_right hp, ite_eq_right hn]
          rw [hstep]
          exact ⟨ham.le, (hmR.trans_le hRu).le, Or.inr ⟨hmx, hmx⟩⟩
    · rcases hit with ⟨hL, hR⟩
      have hm : ((bisect f a u n).1 + (bisect f a u n).2) / 2 = x := by rw [hL, hR]; ring
      have hstep : bisect f a u (n + 1) = (x, x) := by
        simp only [bisect, bisectStep, hm, hx, lt_self_iff_false, ↓reduceIte]
      rw [hstep]
      exact ⟨hax.le, hxu.le, Or.inr ⟨rfl, rfl⟩⟩

theorem bisect_bracket {f : ℝ → ℝ} {a u x : ℝ}
    (hax : a < x) (hxu : x < u) (hx : f x = 0)
    (hpos : ∀ y, a < y → y < x → 0 < f y)
    (hneg : ∀ y, x < y → f y < 0) (n : ℕ) :
    a ≤ (bisect f a u n).1 ∧ (bisect f a u n).1 ≤ x ∧
    x ≤ (bisect f a u n).2 ∧ (bisect f a u n).2 ≤ u ∧
    (bisect f a u n).2 - (bisect f a u n).1 ≤ (u - a) / (2 : ℝ) ^ n := by
  rcases bisect_invariant hax hxu hx hpos hneg n with ⟨hL, hR, hs | hs⟩
  · exact ⟨hL, hs.1.le, hs.2.1.le, hR, hs.2.2.le⟩
  · rcases hs with ⟨hl, hr⟩
    refine ⟨hL, hl.le, hr.ge, hR, ?_⟩
    rw [hl, hr, sub_self]
    exact div_nonneg (sub_nonneg.mpr (hax.trans hxu).le) (by positivity)

theorem bisect_width_before_hit {f : ℝ → ℝ} {a u x : ℝ}
    (hax : a < x) (hxu : x < u) (hx : f x = 0)
    (hpos : ∀ y, a < y → y < x → 0 < f y)
    (hneg : ∀ y, x < y → f y < 0) (n : ℕ)
    (hne : (bisect f a u n).1 ≠ (bisect f a u n).2) :
    (bisect f a u n).1 < x ∧ x < (bisect f a u n).2 ∧
    (bisect f a u n).2 - (bisect f a u n).1 = (u - a) / (2 : ℝ) ^ n := by
  rcases (bisect_invariant hax hxu hx hpos hneg n).2.2 with hs | hs
  · exact hs
  · exact False.elim (hne (hs.1.trans hs.2.symm))


/-- `Nat.ceil` automatically truncates the logarithmic step count at zero. -/
def bisectionSteps (C δ : ℝ) : ℕ := ⌈Real.log (C / δ) / Real.log 2⌉₊

theorem bisectionSteps_bound {C δ : ℝ} (hC : 0 < C) (hδ : 0 < δ) :
    C / (2 : ℝ) ^ bisectionSteps C δ ≤ δ := by
  have ht : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn : Real.log (C / δ) / Real.log 2 ≤ (bisectionSteps C δ : ℝ) := Nat.le_ceil _
  have hlog : Real.log (C / δ) ≤ Real.log ((2 : ℝ) ^ bisectionSteps C δ) := by
    rw [Real.log_pow]
    exact (div_le_iff₀ ht).mp hn
  have hpow : C / δ ≤ (2 : ℝ) ^ bisectionSteps C δ :=
    (Real.log_le_log_iff (div_pos hC hδ) (by positivity)).mp hlog
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ bisectionSteps C δ)).mpr
  have hh := (div_le_iff₀ hδ).mp hpow
  nlinarith

theorem geometric_enclosure_tendsto (l r : ℕ → ℝ) (x C : ℝ)
    (hbr : ∀ n, l n ≤ x ∧ x ≤ r n)
    (hw : ∀ n, r n - l n ≤ C / (2 : ℝ) ^ n) :
    Filter.Tendsto l Filter.atTop (nhds x) ∧
    Filter.Tendsto r Filter.atTop (nhds x) := by
  have hzero : Filter.Tendsto (fun n : ℕ => C / (2 : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hl : Filter.Tendsto (fun n => x - l n) Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun n => sub_nonneg.mpr (hbr n).1) _ hzero
    intro n
    have := hw n
    have := (hbr n).2
    linarith
  have hr : Filter.Tendsto (fun n => r n - x) Filter.atTop (nhds 0) := by
    apply squeeze_zero (fun n => sub_nonneg.mpr (hbr n).2) _ hzero
    intro n
    have := hw n
    have := (hbr n).1
    linarith
  constructor
  · have ht := tendsto_const_nhds.sub hl (a := x)
    simpa only [sub_sub_cancel, sub_zero] using ht
  · have ht := hr.add_const x
    simpa only [sub_add_cancel, zero_add] using ht


/-- The brackets in the exact-arithmetic corollary, with exact hits retained. -/
def bisectionInterval (ε c : ℝ) (n : ℕ) : ℝ × ℝ :=
  bisect (F (paramA ε) c) (paramA ε) (U (paramA ε) c) n

def bisectionLowerValue (ε c : ℝ) (n : ℕ) : ℝ :=
  ε ^ 2 * hp c (bisectionInterval ε c n).1 / (2 * (bisectionInterval ε c n).2)

def bisectionUpperValue (ε c : ℝ) (n : ℕ) : ℝ :=
  ε ^ 2 * hp c (bisectionInterval ε c n).2 / (2 * (bisectionInterval ε c n).1)

/-- All finite-step certificates use the actual analytic objective and value. -/
structure BisectionEnclosure (ε c x : ℝ) (n : ℕ) : Prop where
  left_bound : paramA ε ≤ (bisectionInterval ε c n).1
  right_bound : (bisectionInterval ε c n).2 ≤ U (paramA ε) c
  contains : (bisectionInterval ε c n).1 ≤ x ∧ x ≤ (bisectionInterval ε c n).2
  root_or_exact_width :
    (((bisectionInterval ε c n).1 < x ∧ x < (bisectionInterval ε c n).2 ∧
      (bisectionInterval ε c n).2 - (bisectionInterval ε c n).1 =
        (U (paramA ε) c - paramA ε) / (2 : ℝ) ^ n) ∨
      ((bisectionInterval ε c n).1 = x ∧ (bisectionInterval ε c n).2 = x))
  order_enclosure :
    pointOrder ε (bisectionInterval ε c n).1 ≤ pointOrder ε x ∧
    pointOrder ε x ≤ pointOrder ε (bisectionInterval ε c n).2
  order_width :
    pointOrder ε (bisectionInterval ε c n).2 - pointOrder ε (bisectionInterval ε c n).1 ≤
      ((U (paramA ε) c - paramA ε) / (2 : ℝ) ^ n) / ε
  value_enclosure :
    bisectionLowerValue ε c n ≤ ε ^ 2 * d c x ∧
    ε ^ 2 * d c x ≤ bisectionUpperValue ε c n
  value_width :
    bisectionUpperValue ε c n - bisectionLowerValue ε c n ≤
      ((ε + 2) * (U (paramA ε) c - paramA ε)) / (2 : ℝ) ^ n

lemma hp_div_eq_d (c x : ℝ) : hp c x / (2 * x) = d c x := by
  unfold hp d
  rw [div_div]
  congr 1
  ring

theorem bisection_enclosure {ε c x : ℝ} (he : 0 < ε) (hc : 0 ≤ c)
    (hs : InteriorShape (paramA ε) c x) (n : ℕ) : BisectionEnclosure ε c x n := by
  have hb := bisect_bracket hs.lower hs.upper hs.root hs.positive hs.negative n
  change paramA ε ≤ (bisectionInterval ε c n).1 ∧
    (bisectionInterval ε c n).1 ≤ x ∧ x ≤ (bisectionInterval ε c n).2 ∧
    (bisectionInterval ε c n).2 ≤ U (paramA ε) c ∧
    (bisectionInterval ε c n).2 - (bisectionInterval ε c n).1 ≤
      (U (paramA ε) c - paramA ε) / (2 : ℝ) ^ n at hb
  have hLpos : 0 < (bisectionInterval ε c n).1 :=
    lt_of_lt_of_le (paramA_pos he) hb.1
  have hLR := hb.2.1.trans hb.2.2.1
  have hhp := hp_nonneg hc hLpos.le
  have hv := bisection_value_enclosure (hp c) he hb.1 hb.2.1 hb.2.2.1 hhp
    (monotone_hp hc hb.2.1) (monotone_hp hc hb.2.2.1)
  rw [hp_div_eq_d] at hv
  have hw := bisection_value_width (hp c) he hb.1 hLR hhp
    (hp_le_one hc _) (monotone_hp hc hLR) (hp_sub_le_sub hc hLR)
  refine ⟨hb.1, hb.2.2.2.1, ⟨hb.2.1, hb.2.2.1⟩,
    (bisect_invariant hs.lower hs.upper hs.root hs.positive hs.negative n).2.2,
    ?_, ?_, hv, ?_⟩
  · exact ⟨(pointOrder_strictMono he).monotone hb.2.1,
      (pointOrder_strictMono he).monotone hb.2.2.1⟩
  · unfold pointOrder
    have hh := div_le_div_of_nonneg_right hb.2.2.2.2 he.le
    rw [sub_div] at hh
    linarith
  · change ε ^ 2 * hp c (bisectionInterval ε c n).2 / (2 * (bisectionInterval ε c n).1) -
      ε ^ 2 * hp c (bisectionInterval ε c n).1 / (2 * (bisectionInterval ε c n).2) ≤ _
    calc
      _ ≤ (ε + 2) * ((bisectionInterval ε c n).2 - (bisectionInterval ε c n).1) := hw
      _ ≤ (ε + 2) * ((U (paramA ε) c - paramA ε) / (2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hb.2.2.2.2 (by linarith)
      _ = _ := by ring

/-- Prior to an exact hit, the order bracket is strict and has the stated exact width. -/
theorem bisection_order_before_hit {ε c x : ℝ} (he : 0 < ε)
    (hs : InteriorShape (paramA ε) c x) (n : ℕ)
    (hne : (bisectionInterval ε c n).1 ≠ (bisectionInterval ε c n).2) :
    pointOrder ε (bisectionInterval ε c n).1 < pointOrder ε x ∧
    pointOrder ε x < pointOrder ε (bisectionInterval ε c n).2 ∧
    pointOrder ε (bisectionInterval ε c n).2 - pointOrder ε (bisectionInterval ε c n).1 =
      ((U (paramA ε) c - paramA ε) / (2 : ℝ) ^ n) / ε := by
  have hb := bisect_width_before_hit hs.lower hs.upper hs.root hs.positive hs.negative n hne
  refine ⟨pointOrder_strictMono he hb.1, pointOrder_strictMono he hb.2.1, ?_⟩
  calc
    _ = ((bisectionInterval ε c n).2 - (bisectionInterval ε c n).1) / ε := by
      unfold pointOrder
      ring
    _ = _ := congrArg (fun t : ℝ => t / ε) hb.2.2

/-- The finite brackets and the value bounds converge, including after an exact hit. -/
theorem bisection_convergence {ε c x : ℝ} (he : 0 < ε) (hc : 0 ≤ c)
    (hs : InteriorShape (paramA ε) c x) :
    (Filter.Tendsto (fun n => (bisectionInterval ε c n).1) Filter.atTop (nhds x) ∧
     Filter.Tendsto (fun n => (bisectionInterval ε c n).2) Filter.atTop (nhds x)) ∧
    (Filter.Tendsto (bisectionLowerValue ε c) Filter.atTop (nhds (ε ^ 2 * d c x)) ∧
     Filter.Tendsto (bisectionUpperValue ε c) Filter.atTop (nhds (ε ^ 2 * d c x))) := by
  constructor
  · apply geometric_enclosure_tendsto _ _ x (U (paramA ε) c - paramA ε)
    · intro n
      exact (bisection_enclosure he hc hs n).contains
    · intro n
      exact (bisect_bracket hs.lower hs.upper hs.root hs.positive hs.negative n).2.2.2.2
  · apply geometric_enclosure_tendsto _ _ (ε ^ 2 * d c x)
      ((ε + 2) * (U (paramA ε) c - paramA ε))
    · intro n
      exact (bisection_enclosure he hc hs n).value_enclosure
    · intro n
      exact (bisection_enclosure he hc hs n).value_width

/-- The published logarithmic count suffices for any prescribed value width. -/
theorem bisection_iteration_bound {ε c x δ : ℝ} (he : 0 < ε) (hc : 0 ≤ c)
    (hs : InteriorShape (paramA ε) c x) (hδ : 0 < δ) :
    let N := bisectionSteps ((ε + 2) * (U (paramA ε) c - paramA ε)) δ
    bisectionUpperValue ε c N - bisectionLowerValue ε c N ≤ δ := by
  dsimp
  apply le_trans (bisection_enclosure he hc hs _).value_width
  apply bisectionSteps_bound _ hδ
  have haU := hs.lower.trans hs.upper
  exact mul_pos (by linarith) (sub_pos.mpr haU)

/-- Complete bisection corollary from the original parameter regime. -/
theorem bisection_corollary {k : ℕ} {ε : ℝ} (hk : 2 ≤ k) (he : 0 < ε)
    (hthreshold : threshold ε < (k : ℝ)) :
    ∃ x, InteriorShape (paramA ε) (paramC k ε) x ∧
      (∀ n, BisectionEnclosure ε (paramC k ε) x n) ∧
      (Filter.Tendsto (fun n => (bisectionInterval ε (paramC k ε) n).1)
        Filter.atTop (nhds x) ∧
       Filter.Tendsto (fun n => (bisectionInterval ε (paramC k ε) n).2)
        Filter.atTop (nhds x)) ∧
      (Filter.Tendsto (bisectionLowerValue ε (paramC k ε))
        Filter.atTop (nhds (ε ^ 2 * d (paramC k ε) x)) ∧
       Filter.Tendsto (bisectionUpperValue ε (paramC k ε))
        Filter.atTop (nhds (ε ^ 2 * d (paramC k ε) x))) ∧
      (∀ δ > 0,
        let N := bisectionSteps ((ε + 2) * (U (paramA ε) (paramC k ε) - paramA ε)) δ
        bisectionUpperValue ε (paramC k ε) N - bisectionLowerValue ε (paramC k ε) N ≤ δ) := by
  have hc := paramC_nonneg hk ε
  obtain ⟨x, hs⟩ := interior_shape (paramA_pos he) hc ((g_param_pos_iff he).mpr hthreshold)
  have hlim := bisection_convergence he hc hs
  exact ⟨x, hs, bisection_enclosure he hc hs, hlim.1, hlim.2,
    fun δ hδ => bisection_iteration_bound he hc hs hδ⟩

end
end ExactZCDP
