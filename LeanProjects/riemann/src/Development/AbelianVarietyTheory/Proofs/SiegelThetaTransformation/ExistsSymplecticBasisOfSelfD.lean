import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level

theorem GlobalTheory.Ker.exists_symplectic_basis_of_selfD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r), SelfD X X.Λ →
    ∃ (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (_ : Fin g ≃ X.Ψ × Fin r), IsSympl X bas := by
  intro E _ _ _ r X hL

  obtain ⟨bas, hbas⟩ := GlobalTheory.Dict.Letters.exists_isSympl X hL (Fintype.equivFin (X.Ψ × Fin r)).symm
  exact ⟨_, bas, (Fintype.equivFin _).symm, hbas⟩
