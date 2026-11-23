import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.ProdSubquot
open TensorProduct

section General
variable {G H V V' W W' : Type} [Group G] [Group H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem isSubquotient_extTensor_left {σ : Representation ℂ G V} {σ' : Representation ℂ G V'}
    (B : Representation ℂ H W) (h : IsSubquotient σ σ') :
    IsSubquotient (extTensor σ B) (extTensor σ' B) := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap σ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨ι', hι'⟩ := GlobalTheory.ParIndExact.extTensor_injective_left B ι hι
  have hs : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapLeft B f) :=
    LinearMap.rTensor_surjective W hf
  exact (IsSubquotient.of_surjective _ hs).trans (IsSubquotient.of_injective ι' hι')

theorem isSubquotient_extTensor_right {ρ : Representation ℂ H W} {ρ' : Representation ℂ H W'}
    (A : Representation ℂ G V) (h : IsSubquotient ρ ρ') :
    IsSubquotient (extTensor A ρ) (extTensor A ρ') := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap ρ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  obtain ⟨ι', hι'⟩ := GlobalTheory.ParIndExact.extTensor_injective_right A ι hι
  have hs : Function.Surjective (GlobalTheory.ParIndExact.extTensorMapRight A f) :=
    LinearMap.lTensor_surjective V hf
  exact (IsSubquotient.of_surjective _ hs).trans (IsSubquotient.of_injective ι' hι')

theorem isSubquotient_comp {L : Type} [Group L] {σ : Representation ℂ G V}
    {σ' : Representation ℂ G V'} (s : L →* G) (h : IsSubquotient σ σ') :
    IsSubquotient (σ.comp s) (σ'.comp s) := by
  obtain ⟨S, f, hf⟩ := h
  let T : Subrepresentation (σ'.comp s) :=
    ⟨S.toSubmodule, fun x _ hv => S.apply_mem_toSubmodule (s x) hv⟩
  exact ⟨T, ⟨f.toLinearMap, fun x => f.isIntertwining' (s x)⟩, hf⟩

end General

theorem prod₂_isSubquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (U U' W W' : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U) (σ' : Representation ℂ (GL (Fin r) k) U') (ρ : Representation ℂ (GL (Fin t) k) W) (ρ' : Representation ℂ (GL (Fin t) k) W'), IsSmooth σ' → IsSmooth ρ' → IsSubquotient σ σ' → IsSubquotient ρ ρ' → IsSubquotient (prod₂ σ ρ) (prod₂ σ' ρ') := by
  intro k _ _ _ _ r t U U' W W' _ _ _ _ _ _ _ _ σ σ' ρ ρ' hσ' hρ' hs hr
  have hext : IsSubquotient (extTensor σ ρ) (extTensor σ' ρ') :=
    (isSubquotient_extTensor_left ρ hs).trans (isSubquotient_extTensor_right σ' hr)
  have hsm : IsSmooth ((extTensor σ' ρ').comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) :=
    isSmooth_comp (isSmooth_extTensor hσ' hρ') _
      (show Continuous fun g : Levi k (Two (Fin r) (Fin t)) => (g false, g true) from
        (continuous_apply false).prodMk (continuous_apply true))
  exact GlobalTheory.ParIndSubquot.parInd_isSubquotient k _ _ _ _ _ _ _ _ hsm
    (isSubquotient_comp _ hext)

end GlobalTheory.CompanionTheory.ProdSubquot
