import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSemisimple
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands

namespace GlobalTheory.WeilDeligne.PrimDecomp

theorem exists_stable_isCompl : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (S : Submodule ℂ V), (∀ σ, ∀ v ∈ S, a.ρ σ v ∈ S) → ∃ T : Submodule ℂ V, IsCompl S T ∧ ∀ σ, ∀ v ∈ T, a.ρ σ v ∈ T := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a S hS
  haveI := isSemisimpleRepresentation_of_isSmooth a.ρ a.smooth a.semisimple
  obtain ⟨T, hT⟩ := exists_isCompl (⟨S, fun σ v hv => hS σ v hv⟩ : Subrepresentation a.ρ)
  refine ⟨T.toSubmodule, ?_, fun σ v hv => T.apply_mem_toSubmodule σ hv⟩
  exact IsCompl.of_eq (congrArg Subrepresentation.toSubmodule hT.inf_eq_bot)
    (congrArg Subrepresentation.toSubmodule hT.sup_eq_top)

end GlobalTheory.WeilDeligne.PrimDecomp
