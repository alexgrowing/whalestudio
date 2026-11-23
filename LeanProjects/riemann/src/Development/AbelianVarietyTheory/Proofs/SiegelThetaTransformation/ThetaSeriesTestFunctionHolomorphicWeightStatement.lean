import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_testFunction_holomorphic_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (φ : TF n g), IsSB φ → ∀ P ∈ Harm.rowHighest ℂ c c', DifferentiableOn ℂ (thP X hr bas idx φ P) X.dom ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, thP X hr bas idx φ P (rmul x b) = bchar (wtOf X hr c c' n) b * thP X hr bas idx φ P x) ∧ (∀ γ, IsUn X γ → ∀ x ∈ X.dom, thP X hr bas idx (wG X bas idx γ φ) P (lact γ x) = thP X hr bas idx φ P x) ∧ ∀ x ∈ X.dom, AnalyticOnNhd ℂ (thA X bas idx φ x) Set.univ := by
  first | exact @GlobalTheory.SW.theta_holomorphic_weight | exact GlobalTheory.SW.theta_holomorphic_weight | (intros; apply GlobalTheory.SW.theta_holomorphic_weight <;> assumption)
