import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! Definitions used in the exact zCDP characterization of k-ary randomized response. -/

namespace ExactZCDP

noncomputable section

def h (c x : ℝ) : ℝ := Real.log (c + Real.cosh x)
def hp (c x : ℝ) : ℝ := Real.sinh x / (c + Real.cosh x)
def d (c x : ℝ) : ℝ := Real.sinh x / (2 * x * (c + Real.cosh x))
def g (c x : ℝ) : ℝ :=
  x * (1 + c * Real.cosh x) - Real.sinh x * (c + Real.cosh x)
def F (a c x : ℝ) : ℝ := (x ^ 2 - a ^ 2) * d c x - h c x + h c a
def Q (a c x : ℝ) : ℝ := (h c x - h c a) / (x ^ 2 - a ^ 2)
def U (a c : ℝ) : ℝ := 2 * Real.log (2 * (c + Real.cosh a))

def normalizer (k : ℕ) (ε : ℝ) : ℝ := Real.exp ε + k - 1
def paramA (ε : ℝ) : ℝ := ε / 2
def paramC (k : ℕ) (ε : ℝ) : ℝ := (k - 2 : ℝ) / (2 * Real.exp (paramA ε))
def threshold (ε : ℝ) : ℝ :=
  2 * (Real.exp ε - 1) * (Real.exp ε - 1 - ε) /
    (ε * (Real.exp ε + 1) - 2 * Real.exp ε + 2)
def endpointValue (k : ℕ) (ε : ℝ) : ℝ :=
  ε * (Real.exp ε - 1) / normalizer k ε
def profile (k : ℕ) (ε α : ℝ) : ℝ :=
  Real.log ((Real.exp (α * ε) + Real.exp ((1 - α) * ε) + k - 2) /
    normalizer k ε) / (α * (α - 1))
def orderPoint (ε α : ℝ) : ℝ := ε * (α - 1 / 2)
def pointOrder (ε x : ℝ) : ℝ := 1 / 2 + x / ε

end
end ExactZCDP
