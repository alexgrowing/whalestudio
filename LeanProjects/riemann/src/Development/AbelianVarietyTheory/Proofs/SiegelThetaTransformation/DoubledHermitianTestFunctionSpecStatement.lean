import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledHermitianTestFunctionSpec
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledHermitianTestFunction_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → IsSB (dbl X bas idx φ₁ φ₂) ∧ IsDbl X bas idx φ₁ φ₂ (dbl X bas idx φ₁ φ₂) ∧ ∀ ψ, IsSB ψ → IsDbl X bas idx φ₁ φ₂ ψ → ψ = dbl X bas idx φ₁ φ₂ := by
  first | exact @GlobalTheory.SW.DblEx.dbl_spec | exact GlobalTheory.SW.DblEx.dbl_spec | (intros; apply GlobalTheory.SW.DblEx.dbl_spec <;> assumption)
