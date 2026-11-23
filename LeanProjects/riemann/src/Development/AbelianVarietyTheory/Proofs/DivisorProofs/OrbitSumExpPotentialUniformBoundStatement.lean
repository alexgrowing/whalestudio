import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumExpPotentialUniformBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitSum_exp_potential_uniform_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ s : ℝ, 0 < s → (∃ I : ℝ≥0∞, I < ⊤ ∧ ∀ x1 : Frame X.Ψ r, IsOrth X x1 → ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x1 z))) ∂muF X x1 ≤ I) → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x → ∑' γ : X.Γ, ENNReal.ofReal (Real.exp (-(s * GlobalTheory.Up.rhX X x0 (lact γ.1 x)))) ≤ C := by
  first | exact @GlobalTheory.OrbitSum.orbitSum_le | exact GlobalTheory.OrbitSum.orbitSum_le | (intros; apply GlobalTheory.OrbitSum.orbitSum_le <;> assumption)
