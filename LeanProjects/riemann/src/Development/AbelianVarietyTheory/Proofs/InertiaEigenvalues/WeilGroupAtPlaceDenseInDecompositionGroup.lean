import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupActsResiduesFrobeniusPowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixingActsAsFrobeniusPowerResidueStatement

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_weil_apply_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w),
    ∀ d ∈ Dec (F := E) A, ∀ y : Ω, ∃ τ ∈ Weil h, τ y = d y := by
  intro E Ω _ _ _ _ _ A w h d hd y
  obtain ⟨K, hK, hy, j, hj⟩ := GlobalTheory.T.decompositionGroup_acts_residues_frobeniusPower E Ω A w h d hd y
  obtain ⟨ρ, hρK, hρ⟩ := GlobalTheory.T.exists_fixing_actsAsFrobeniusPowerResidue E Ω A w h K d hd j hj
  refine ⟨d * ρ, (mem_Weil h).2 ⟨j, 0, hρ⟩, ?_⟩
  rw [AlgEquiv.mul_apply, hρK y hy]

end GlobalTheory.WeilDeligne
