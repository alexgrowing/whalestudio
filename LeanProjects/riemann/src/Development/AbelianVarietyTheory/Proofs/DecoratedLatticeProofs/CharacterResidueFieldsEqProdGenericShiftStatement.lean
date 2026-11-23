import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterResidueFieldsEqProdGenericShift
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_residueFields_eq_prod_genericShift : ∀ (E : Type) [Field E] [NumberField E] (S : Type) [CommRing S] (Pg : Finset (Pl E)) (p p' : ∀ PP : Pl E, S →+* kP PP) (χ : S → ℂ) (ψ0 : ∀ PP : Pl E, AddChar (kP PP) ℂ), IsGenericPsi Pg ψ0 → (∀ s t, χ (s + t) = χ s * χ t) → (∀ s, (∀ PP ∈ Pg, p PP s = 0 ∧ p' PP s = 0) → χ s = 1) → (∀ u u' : ∀ PP : Pl E, kP PP, ∃ s, ∀ PP ∈ Pg, p PP s = u PP ∧ p' PP s = u' PP) → (∀ PP ∈ Pg, (∃ s, (∀ PP' ∈ Pg, (PP' ≠ PP → p PP' s = 0) ∧ p' PP' s = 0) ∧ χ s ≠ 1) ∧ ∃ s, (∀ PP' ∈ Pg, p PP' s = 0 ∧ (PP' ≠ PP → p' PP' s = 0)) ∧ χ s ≠ 1) → ∃ a₁ a₂ : ∀ PP : Pl E, kP PP, (∀ PP ∈ Pg, a₁ PP ≠ 0 ∧ a₂ PP ≠ 0) ∧ ∀ s, χ s = ∏ PP ∈ Pg, ψ0 PP (a₁ PP * p PP s + a₂ PP * p' PP s) := by
  first | exact @GlobalTheory.LeviBlockCharacter.char_eq_prod_shift | exact GlobalTheory.LeviBlockCharacter.char_eq_prod_shift | (intros; apply GlobalTheory.LeviBlockCharacter.char_eq_prod_shift <;> assumption)
