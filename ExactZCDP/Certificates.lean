import ExactZCDP.Main
import ExactZCDP.Bisection

/-! Bisection certificates for the least parameter of the actual mechanism. -/

namespace ExactZCDP

noncomputable section

variable {k : ℕ} {ε δ : ℝ}

/-- Every exact-arithmetic step encloses both the unique optimizer and the least parameter. -/
theorem exact_bisection_certificate (hk : 2 ≤ k) (he : 0 < ε)
    (hK : threshold ε < (k : ℝ)) (n : ℕ) :
    BisectionEnclosure ε (paramC k ε) (interiorPoint (paramA ε) (paramC k ε)) n ∧
    bisectionLowerValue ε (paramC k ε) n ≤ exactParameter k ε ∧
    exactParameter k ε ≤ bisectionUpperValue ε (paramC k ε) n := by
  have hs := interiorPoint_spec (paramA_pos he) (paramC_nonneg hk ε)
    ((g_param_pos_iff he).2 hK)
  have hb := bisection_enclosure he (paramC_nonneg hk ε) hs n
  refine ⟨hb, ?_⟩
  rw [exactParameter_interior hk he hK hs]
  exact hb.value_enclosure

/-- Both value certificates converge to the least zCDP parameter. -/
theorem exact_bisection_converges (hk : 2 ≤ k) (he : 0 < ε)
    (hK : threshold ε < (k : ℝ)) :
    Filter.Tendsto (bisectionLowerValue ε (paramC k ε)) Filter.atTop
      (nhds (exactParameter k ε)) ∧
    Filter.Tendsto (bisectionUpperValue ε (paramC k ε)) Filter.atTop
      (nhds (exactParameter k ε)) := by
  have hs := interiorPoint_spec (paramA_pos he) (paramC_nonneg hk ε)
    ((g_param_pos_iff he).2 hK)
  rw [exactParameter_interior hk he hK hs]
  exact (bisection_convergence he (paramC_nonneg hk ε) hs).2

/-- The published iteration count produces a certificate of any positive requested width. -/
theorem exact_bisection_iteration_bound (hk : 2 ≤ k) (he : 0 < ε)
    (hK : threshold ε < (k : ℝ)) (hδ : 0 < δ) :
    let N := bisectionSteps ((ε + 2) * (U (paramA ε) (paramC k ε) - paramA ε)) δ
    bisectionLowerValue ε (paramC k ε) N ≤ exactParameter k ε ∧
    exactParameter k ε ≤ bisectionUpperValue ε (paramC k ε) N ∧
    bisectionUpperValue ε (paramC k ε) N - bisectionLowerValue ε (paramC k ε) N ≤ δ := by
  dsimp
  have hs := interiorPoint_spec (paramA_pos he) (paramC_nonneg hk ε)
    ((g_param_pos_iff he).2 hK)
  have hb := exact_bisection_certificate hk he hK
    (bisectionSteps ((ε + 2) * (U (paramA ε) (paramC k ε) - paramA ε)) δ)
  exact ⟨hb.2.1, hb.2.2, bisection_iteration_bound he (paramC_nonneg hk ε) hs hδ⟩

end
end ExactZCDP
