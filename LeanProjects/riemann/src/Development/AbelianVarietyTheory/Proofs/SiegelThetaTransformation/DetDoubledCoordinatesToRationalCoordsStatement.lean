import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetDoubledCoordinatesToRationalCoords
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_doubledCoordinates_to_rationalCoords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (idx : Fin g ≃ X.Ψ × Fin r) (e : (Fin g ⊕ Fin g) ≃ QI E r), ∃ c : ℂ, ∀ x₁ x₂ : Frame X.Ψ r, ∃ L : Matrix (QI E r) (Fin g ⊕ Fin g) ℂ, (L.submatrix e id).det = c * ∏ τ : X.Ψ, ((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det)⁻¹ ∧ ∀ (n : ℕ) (z₁ w : Fin n → Fin g → ℂ) (k : Fin n), zetaOf X.Ψ (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w) k = L *ᵥ Sum.elim (z₁ k) (w k) := by
  first | exact @GlobalTheory.SW.det_dbl_coords | exact GlobalTheory.SW.det_dbl_coords | (intros; apply GlobalTheory.SW.det_dbl_coords <;> assumption)
