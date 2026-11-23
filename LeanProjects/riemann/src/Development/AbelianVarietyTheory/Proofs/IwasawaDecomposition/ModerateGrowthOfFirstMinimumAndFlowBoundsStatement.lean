import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModerateGrowthOfFirstMinimumAndFlowBounds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderate_growth_of_firstMinimum_and_flow_bounds : FlowMajSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (w : ℝ) (φ : Frame X.Ψ r → ℝ), 0 ≤ w → (∀ x ∈ X.dom, 0 ≤ φ x) → ThickBdd X φ → StepBound X w φ → ∃ C A : ℝ, ∀ x ∈ X.dom, φ x ≤ C * X.la1 x ^ (-(A * w)) := by
  first | exact @GlobalTheory.CuspDescent.moderate_of_stepBound | exact GlobalTheory.CuspDescent.moderate_of_stepBound | (intros; apply GlobalTheory.CuspDescent.moderate_of_stepBound <;> assumption)
