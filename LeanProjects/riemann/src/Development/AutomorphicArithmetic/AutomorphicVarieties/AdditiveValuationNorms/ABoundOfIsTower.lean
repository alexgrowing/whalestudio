import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ABoundOfDescends
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.GenLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.Descends

open NumberField Formalism.GaloisCohomology

theorem UpperTheory.V.PropA.aBound_of_isTower (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (l : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀] [NumberField L₀] (R : ℕ) (ht : UpperTheory.V.Tower.IsTower l L₀ R) :
    UpperTheory.V.Win.ABound l R L₀ := by
  obtain ⟨γ, h₁, h₂, h₃⟩ := UpperTheory.V.PropA.genLevel l L₀ ht.mu
  exact UpperTheory.V.PropA.aBound_of_descends hP hF hT ht h₂ h₃ (UpperTheory.V.PropA.descends l L₀ ht.mu γ h₁)
