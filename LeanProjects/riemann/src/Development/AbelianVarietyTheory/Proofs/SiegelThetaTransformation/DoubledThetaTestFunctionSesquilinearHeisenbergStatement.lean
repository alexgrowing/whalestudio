import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledThetaTestFunctionSesquilinearHeisenberg
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → (∀ ψ, IsSB ψ → dbl X bas idx (φ₁ + ψ) φ₂ = dbl X bas idx φ₁ φ₂ + dbl X bas idx ψ φ₂ ∧ dbl X bas idx φ₁ (φ₂ + ψ) = dbl X bas idx φ₁ φ₂ + dbl X bas idx φ₁ ψ) ∧ (∀ a b : ℂ, dbl X bas idx (a • φ₁) (b • φ₂) = (a * conj b) • dbl X bas idx φ₁ φ₂) ∧ ∀ y₁ y₂ : Matrix (Fin n) (Fin r) E, dbl X bas idx (heisG X bas y₁ φ₁) (heisG X bas y₂ φ₂) = heisH (Matrix.fromCols y₁ y₂ * dblT X).toCols₁ (Matrix.fromCols y₁ y₂ * dblT X).toCols₂ (dbl X bas idx φ₁ φ₂) := by
  first | exact @GlobalTheory.SW.DblLin.dbl_lin | exact GlobalTheory.SW.DblLin.dbl_lin | (intros; apply GlobalTheory.SW.DblLin.dbl_lin <;> assumption)
