import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

theorem UpperTheory.V.LDataCardLeFinrank.imageConj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A A' : ValuationSubring Ω), IsPlaceOver A v → IsPlaceOver A' v → decImage F l A = decImage F l A' ∧ ineImage F l A = ineImage F l A' := by
  intro F Ω _ _ _ _ _ l _ v
  have hc : ∀ g σ : G F Ω, cycZ F Ω l (g⁻¹ * σ * g) = cycZ F Ω l σ := fun g σ => by
    rw [map_mul, map_mul, map_inv, mul_comm _ (cycZ F Ω l σ), inv_mul_cancel_right]
  have key : ∀ A A' : ValuationSubring Ω, IsPlaceOver A v → IsPlaceOver A' v →
      decImage F l A' ≤ decImage F l A ∧ ineImage F l A' ≤ ineImage F l A := by
    intro A A' hA hA'
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA hA'
    constructor
    · rintro _ ⟨σ, hσ, rfl⟩
      exact ⟨_, GlobalTheory.Cut.ShaBound.conj_mem_Dec hσ, hc g σ⟩
    · rintro _ ⟨σ, hσ, rfl⟩
      exact ⟨_, GlobalTheory.Cut.ShaBound.conj_mem_Ine' hσ, hc g σ⟩
  intro A A' hA hA'
  exact ⟨le_antisymm (key A' A hA' hA).1 (key A A' hA hA').1,
    le_antisymm (key A' A hA' hA).2 (key A A' hA hA').2⟩
