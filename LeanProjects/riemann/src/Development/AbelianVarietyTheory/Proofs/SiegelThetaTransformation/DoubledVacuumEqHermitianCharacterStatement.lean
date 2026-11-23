import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledVacuumEqHermitianCharacter
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuum_eq_hermitian_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L₁ L₂ : Lt E r, SelfD X L₁ → SelfD X L₂ → ∀ M : ℕ, 0 < M → ∀ v₁ v₂ : TF n g, IsVac X bas w (tens (stdL E n) L₁) v₁ → IsVac X bas w (tens (stdL E n) L₂) v₂ → ∃ (β : Matrix (Fin r) (Fin r) E) (t : ℂ), ccT β = β ∧ ∀ Λ ∈ Vset E n M, ∀ x, dbl X bas idx (unitv (projA X bas w (tens Λ L₁) v₁)) (unitv (projA X bas w (tens Λ L₂) v₂)) x = if x ∈ tens Λ (L₁ ⊔ L₂) then t * cexp (π * I * ((Algebra.trace ℚ E (x * β * ccT x).trace : ℚ) : ℂ)) else 0 := by
  first | exact @GlobalTheory.SW.dbl_vacuum | exact GlobalTheory.SW.dbl_vacuum | (intros; apply GlobalTheory.SW.dbl_vacuum <;> assumption)
