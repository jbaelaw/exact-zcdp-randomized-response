import ExactZCDP.Base

/-! The finite randomized-response mechanism, its probability laws, and its actual
Rényi divergence. The closed-form profile is derived from the finite sum. -/

namespace ExactZCDP

noncomputable section

open scoped BigOperators

/-- The output probability at `j`, on input `i`, of k-ary randomized response. -/
def rrProb (k : ℕ) (ε : ℝ) (i j : Fin k) : ℝ :=
  if j = i then Real.exp ε / normalizer k ε else 1 / normalizer k ε

/-- Rényi divergence computed from the probability masses themselves. -/
def renyi {k : ℕ} (P Q : Fin k → ℝ) (α : ℝ) : ℝ :=
  Real.log (∑ j, P j ^ α * Q j ^ (1 - α)) / (α - 1)

/-- All pairs of inputs, including equal inputs, satisfy the zCDP inequalities. -/
def IsZCDP (k : ℕ) (ε ρ : ℝ) : Prop :=
  0 ≤ ρ ∧ ∀ (i j : Fin k) (α : ℝ), 1 < α →
    renyi (rrProb k ε i) (rrProb k ε j) α ≤ ρ * α

private theorem rr_normalizer_pos {k : ℕ} (hk : 2 ≤ k) (ε : ℝ) :
    0 < normalizer k ε := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have he := Real.exp_pos ε
  dsimp [normalizer]
  linarith

 theorem rrProb_pos {k : ℕ} (hk : 2 ≤ k) (ε : ℝ) (i j : Fin k) :
    0 < rrProb k ε i j := by
  have hz := rr_normalizer_pos hk ε
  unfold rrProb
  split <;> positivity

 theorem rrProb_sum {k : ℕ} (hk : 2 ≤ k) (ε : ℝ) (i : Fin k) :
    ∑ j, rrProb k ε i j = 1 := by
  have hn := ne_of_gt (rr_normalizer_pos hk ε)
  have hr (j : Fin k) : rrProb k ε i j =
      ((if j = i then Real.exp ε - 1 else 0) + 1) / normalizer k ε := by
    by_cases hji : j = i <;> simp [rrProb, hji]
  simp_rw [hr]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have heq : Real.exp ε - 1 + k = normalizer k ε := by unfold normalizer; ring
  rw [heq, div_self hn]

private theorem rrProb_eq_exp {k : ℕ} (ε : ℝ) (i j : Fin k) :
    rrProb k ε i j = Real.exp (if j = i then ε else 0) / normalizer k ε := by
  by_cases hji : j = i <;> simp [rrProb, hji]

private theorem scaled_exp_moment (u v Z α : ℝ) (hZ : 0 < Z) :
    (Real.exp u / Z) ^ α * (Real.exp v / Z) ^ (1 - α) =
      Real.exp (α * u + (1 - α) * v) / Z := by
  rw [Real.div_rpow (le_of_lt (Real.exp_pos u)) hZ.le,
    Real.div_rpow (le_of_lt (Real.exp_pos v)) hZ.le,
    div_mul_div_comm, ← Real.rpow_add hZ]
  rw [show α + (1 - α) = 1 by ring, Real.rpow_one,
    ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  congr 2
  ring

/-- The finite sum defining Rényi divergence, evaluated for distinct inputs. -/
theorem rr_moment_distinct {k : ℕ} (hk : 2 ≤ k) (ε α : ℝ)
    (i j : Fin k) (hij : i ≠ j) :
    (∑ l, rrProb k ε i l ^ α * rrProb k ε j l ^ (1 - α)) =
      (Real.exp (α * ε) + Real.exp ((1 - α) * ε) + k - 2) /
        normalizer k ε := by
  have hz := rr_normalizer_pos hk ε
  have hji : j ≠ i := Ne.symm hij
  have hterm (l : Fin k) :
      rrProb k ε i l ^ α * rrProb k ε j l ^ (1 - α) =
        ((if l = i then Real.exp (α * ε) - 1 else 0) +
          (if l = j then Real.exp ((1 - α) * ε) - 1 else 0) + 1) /
            normalizer k ε := by
    rw [rrProb_eq_exp, rrProb_eq_exp, scaled_exp_moment _ _ _ _ hz]
    by_cases hli : l = i
    · subst l
      simp [hij]
    · by_cases hlj : l = j
      · subst l
        simp [hji]
      · simp [hli, hlj]
  simp_rw [hterm]
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  congr 1
  ring

 theorem renyi_rr_self {k : ℕ} (hk : 2 ≤ k) (ε α : ℝ) (i : Fin k) :
    renyi (rrProb k ε i) (rrProb k ε i) α = 0 := by
  have hm (l : Fin k) : rrProb k ε i l ^ α * rrProb k ε i l ^ (1 - α) =
      rrProb k ε i l := by
    rw [← Real.rpow_add (rrProb_pos hk ε i l),
      show α + (1 - α) = 1 by ring, Real.rpow_one]
  simp only [renyi, hm, rrProb_sum hk ε i, Real.log_one, zero_div]

/-- The closed form is a theorem about the actual divergence, not its definition. -/
theorem renyi_rr_distinct {k : ℕ} (hk : 2 ≤ k) (ε : ℝ) (i j : Fin k)
    (hij : i ≠ j) {α : ℝ} (hα : 1 < α) :
    renyi (rrProb k ε i) (rrProb k ε j) α = α * profile k ε α := by
  unfold renyi profile
  rw [rr_moment_distinct hk ε α i j hij]
  have ha : α ≠ 0 := by linarith
  have hb : α - 1 ≠ 0 := by linarith
  field_simp

 theorem isZCDP_iff_profile {k : ℕ} (hk : 2 ≤ k) (ε ρ : ℝ) (hρ : 0 ≤ ρ) :
    IsZCDP k ε ρ ↔ ∀ α : ℝ, 1 < α → profile k ε α ≤ ρ := by
  constructor
  · intro h α hα
    let i : Fin k := ⟨0, by omega⟩
    let j : Fin k := ⟨1, by omega⟩
    have hij : i ≠ j := by simp [i, j]
    have hb := h.2 i j α hα
    rw [renyi_rr_distinct hk ε i j hij hα] at hb
    exact (mul_le_mul_iff_right₀ (by linarith : 0 < α)).mp (by simpa [mul_comm] using hb)
  · intro h
    refine ⟨hρ, ?_⟩
    intro i j α hα
    by_cases hij : i = j
    · subst j
      rw [renyi_rr_self hk]
      exact mul_nonneg hρ (by linarith)
    · rw [renyi_rr_distinct hk ε i j hij hα]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (h α hα) (by linarith : 0 ≤ α)

 theorem rrProb_zero {k : ℕ} (i j : Fin k) : rrProb k 0 i j = 1 / (k : ℝ) := by
  simp [rrProb, normalizer]

 theorem renyi_rr_zero {k : ℕ} (hk : 2 ≤ k) (i j : Fin k) (α : ℝ) :
    renyi (rrProb k 0 i) (rrProb k 0 j) α = 0 := by
  have heq : rrProb k 0 j = rrProb k 0 i := by funext l; simp [rrProb_zero]
  rw [heq, renyi_rr_self hk]

 theorem isZCDP_zero_iff {k : ℕ} (hk : 2 ≤ k) (ρ : ℝ) :
    IsZCDP k 0 ρ ↔ 0 ≤ ρ := by
  constructor
  · exact And.left
  · intro hρ
    refine ⟨hρ, ?_⟩
    intro i j α hα
    rw [renyi_rr_zero hk]
    exact mul_nonneg hρ (by linarith)

end
end ExactZCDP
