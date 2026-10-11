import ExactZCDP.Parameters
import ExactZCDP.ShapeBounds

/-! The normalized actual Rényi profile has the claimed right endpoint limit,
independently of which optimization regime applies. -/

namespace ExactZCDP

noncomputable section
open Filter Set
open scoped Topology

 theorem endpoint_profile_limit {k : ℕ} {ε : ℝ} (hk : 2 ≤ k) (he : 0 < ε) :
    Tendsto (profile k ε) (𝓝[>] (1 : ℝ)) (𝓝 (endpointValue k ε)) := by
  have hcont : Continuous (orderPoint ε) := by unfold orderPoint; fun_prop
  have hbase : orderPoint ε 1 = paramA ε := by unfold orderPoint paramA; ring
  have hto : Tendsto (orderPoint ε) (𝓝[>] (1 : ℝ)) (𝓝[>] (paramA ε)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · rw [← hbase]
      exact (hcont.continuousAt : ContinuousAt (orderPoint ε) 1).tendsto.mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with α hα
      exact (orderPoint_gt_paramA_iff he).mpr hα
  have hlim := ((tendsto_Q_right (paramA_pos he) (paramC_nonneg hk ε)).comp hto).const_mul
    (ε ^ 2)
  rw [endpoint_identity hk he] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with α hα
  exact (profile_eq_Q hk he hα).symm

end
end ExactZCDP
