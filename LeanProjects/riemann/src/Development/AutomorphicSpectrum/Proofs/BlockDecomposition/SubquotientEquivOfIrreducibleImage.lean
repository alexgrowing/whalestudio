import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrParIffCuspidalProduct

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.IsoSub

theorem nonempty_equiv_of_isotypic {A M T Q S : Type*} [Ring A] [AddCommGroup M] [Module A M]
    [AddCommGroup T] [Module A T] [AddCommGroup Q] [Module A Q] [AddCommGroup S] [Module A S]
    [IsSimpleModule A S] (h : isotypicComponent A M S = ⊤) (j : T →ₗ[A] M)
    (hj : Function.Injective j) (f : T →ₗ[A] Q) (hf : Function.Surjective f) :
    IsSimpleModule A Q → Nonempty (Q ≃ₗ[A] S) := by
  intro hQ
  have hiso : IsIsotypicOfType A M S := IsIsotypicOfType.of_isotypicComponent_eq_top h
  have hss : IsSemisimpleModule A M := by
    refine IsSemisimpleModule.of_sSup_simples_eq_top (top_le_iff.1 ?_)
    rw [← h]
    exact sSup_le_sSup fun m (hm : Nonempty (m ≃ₗ[A] S)) => IsSimpleModule.congr hm.some
  have hT : IsSemisimpleModule A T := IsSemisimpleModule.of_injective j hj
  obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.ker f)
  let e₁ : C ≃ₗ[A] Q :=
    (Submodule.quotientEquivOfIsCompl _ _ hC).symm.trans (f.quotKerEquivOfSurjective hf)
  have hC' : IsSimpleModule A C := IsSimpleModule.congr e₁
  let e₂ : C ≃ₗ[A] C.map j := Submodule.equivMapOfInjective j hj C
  have hCj : IsSimpleModule A (C.map j) := IsSimpleModule.congr e₂.symm
  obtain ⟨e₃⟩ := hiso (C.map j)
  exact ⟨e₁.symm.trans (e₂.trans e₃)⟩

def inclusion {G Y : Type} [Group G] [AddCommGroup Y] [Module ℂ Y] {R : Representation ℂ G Y}
    (S : Subrepresentation R) : S.toRepresentation.IntertwiningMap R :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

theorem equiv_of_isSubquotient (G : Type) [Group G] (V Y W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (R : Representation ℂ G Y) (σ : Representation ℂ G W)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (hR : ⨆ f : ρ.IntertwiningMap R, LinearMap.range f.toLinearMap = ⊤)
    (hsq : IsSubquotient σ R) : Nonempty (σ.Equiv ρ) := by
  have hρs : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).1 hρ
  have hσs : IsSimpleModule (MonoidAlgebra ℂ G) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).1 hσ
  have htop : Subrepresentation.asSubmodule (GlobalTheory.CuspFactor.spanRep R ρ) = ⊤ := by
    have hX : (GlobalTheory.CuspFactor.spanRep R ρ).toSubmodule = ⊤ := hR
    apply SetLike.coe_injective
    show ((GlobalTheory.CuspFactor.spanRep R ρ).toSubmodule : Set Y) = Set.univ
    rw [hX]
    first
      | rfl
      | exact Submodule.top_coe
      | simp
  have h : isotypicComponent (MonoidAlgebra ℂ G) R.asModule ρ.asModule = ⊤ := by
    rw [← GlobalTheory.CuspFactor.spanRep_asSubmodule R ρ hρ]
    exact htop
  obtain ⟨S, f, hf⟩ := hsq
  let j := Representation.IntertwiningMap.equivLinearMapAsModule _ _
    (GlobalTheory.CompanionTheory.IsoSub.inclusion S)
  have hj : Function.Injective j := by
    first
      | exact Subtype.val_injective
      | (intro x y hxy; exact Subtype.val_injective hxy)
  let f' := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
  have hf' : Function.Surjective f' := by
    first
      | exact hf
      | (intro y; obtain ⟨x, hx⟩ := hf y; exact ⟨x, hx⟩)
  exact (GlobalTheory.CuspFactor.nonempty_equiv_iff σ ρ).2
    (GlobalTheory.CompanionTheory.IsoSub.nonempty_equiv_of_isotypic h j hj f' hf' hσs)

end GlobalTheory.CompanionTheory.IsoSub
