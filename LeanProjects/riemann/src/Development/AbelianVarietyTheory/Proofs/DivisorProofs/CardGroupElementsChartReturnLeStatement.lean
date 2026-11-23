import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardGroupElementsChartReturnLe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_group_elements_chart_return_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (x : Frame X.Ψ r) (ε ρ : ℝ), 0 < r → IsOrth X.toData x → 0 < ε → (r : ℝ) ^ 2 * ρ ≤ 1 / 100 → (∀ γ ∈ X.Γ, ∀ v ∈ X.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ X.L') → (∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v)) → ({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z z' : V (nd X.toData), ‖z‖ ≤ ρ ∧ ‖z'‖ ≤ ρ ∧ ∃ b ∈ Bor X.Ψ r, lact γ (cpt X.toData x z) = rmul (cpt X.toData x z') b}.encard : ℝ≥0∞) ≤ ENNReal.ofReal (multBd E r ε) := by
  first | exact @GlobalTheory.chart_mult_le | exact GlobalTheory.chart_mult_le | (intros; apply GlobalTheory.chart_mult_le <;> assumption)
