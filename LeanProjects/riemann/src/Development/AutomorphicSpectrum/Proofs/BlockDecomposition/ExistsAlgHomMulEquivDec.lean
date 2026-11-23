import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEmbeddingOverPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.DecGal

theorem exists_algHom_mulEquiv_dec : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∃ (ι : Ω →ₐ[F] AlgebraicClosure (v.adicCompletion F)) (e : (AlgebraicClosure (v.adicCompletion F) ≃ₐ[v.adicCompletion F] AlgebraicClosure (v.adicCompletion F)) ≃* Dec (F := F) A), Continuous e ∧ Continuous e.symm ∧ ∀ σ x, ι (((e σ : Dec (F := F) A) : G F Ω) x) = σ (ι x) := by
  intro F Ω _ _ _ _ _ A v h
  obtain ⟨ι, hι⟩ := GlobalTheory.LocDict.exists_isLocEmb F Ω A v h
  obtain ⟨θ, hθ, hθ', hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc F Ω A v h ι hι
  refine ⟨ι, θ.symm, hθ', hθ, fun σ x => ?_⟩
  have := hl (θ.symm σ) x
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.CompanionTheory.DecGal
