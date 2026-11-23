import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvariantChartSetLeMulFundamentalSet
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_invariant_chartSet_le_mul_fundamentalSet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 x : Frame X.Ψ r) (FF A : Set (V (nd X))) (m : ℝ≥0∞) (Φ : Frame X.Ψ r → ℝ≥0∞), IsOrth X x0 → IsOrth X x → IsFundSet X x0 FF → MeasurableSet A → A ⊆ OmF X x → Measurable Φ → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Φ (lact γ x) = Φ x) → (∀ b ∈ Bor X.Ψ r, ∀ x ∈ X.dom, Φ (rmul x b) = Φ x) → (({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ A, ∃ z' ∈ A, ∃ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b}.encard : ℝ≥0∞) ≤ m) → ∫⁻ z in A, Φ (cpt X x z) ∂(muF X x) ≤ m * ∫⁻ z in FF, Φ (cpt X x0 z) ∂(muF X x0) := by
  first | exact @GlobalTheory.Unfold.lintegral_chart_le_mul_fundSet | exact GlobalTheory.Unfold.lintegral_chart_le_mul_fundSet | (intros; apply GlobalTheory.Unfold.lintegral_chart_le_mul_fundSet <;> assumption)
