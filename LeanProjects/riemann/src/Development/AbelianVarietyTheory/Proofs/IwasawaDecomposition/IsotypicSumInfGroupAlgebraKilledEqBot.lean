import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicitiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelsMultiplicityEqual
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

noncomputable section

namespace GlobalTheory.RepCount

theorem iSup_range_homInto_inf_killed_eq_bot : ∀ (H S0 X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (ρ : Representation ℂ H X) (C : Submodule ℂ X) (I : Set (MonoidAlgebra ℂ H)), σ0.IsIrreducible → killed σ0 I = ⊥ → ((⨆ f ∈ homInto σ0 ρ C, LinearMap.range f) ⊓ killed ρ I : Submodule ℂ X) = ⊥ := by
  intro H S0 X _ _ _ _ _ σ0 ρ C I hirr hk
  haveI hS : IsSimpleModule (MonoidAlgebra ℂ H) σ0.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ0).1 hirr
  let N : Submodule (MonoidAlgebra ℂ H) ρ.asModule :=
    ⨆ (f : S0 →ₗ[ℂ] X) (hf : f ∈ homInto σ0 ρ C), LinearMap.range (modMap f hf.2)
  have hN : N ≤ isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule σ0.asModule := by
    refine iSup₂_le fun f hf => ?_
    rcases LinearMap.injective_or_eq_zero (modMap f hf.2) with hi | h0
    · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
    · rw [h0, LinearMap.range_zero]; exact bot_le
  haveI : IsSemisimpleModule (MonoidAlgebra ℂ H) N :=
    IsSemisimpleModule.of_injective _ (Submodule.inclusion_injective hN)
  have hiso : IsIsotypicOfType (MonoidAlgebra ℂ H) N σ0.asModule :=
    (IsIsotypicOfType.isotypicComponent _ _ _).of_injective _ (Submodule.inclusion_injective hN)
  obtain ⟨ι, ⟨e⟩⟩ := hiso.linearEquiv_finsupp
  rw [eq_bot_iff]
  rintro v ⟨hv1, hv2⟩
  rw [Submodule.mem_bot]
  by_contra hv0
  have hvN : ρ.asModuleEquiv.symm v ∈ N := by
    have hle : (⨆ f ∈ homInto σ0 ρ C, LinearMap.range f : Submodule ℂ X) ≤
        (N.restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap := by
      refine iSup₂_le fun f hf => ?_
      rintro _ ⟨s, rfl⟩
      have hfs : ρ.asModuleEquiv.symm (f s) = modMap f hf.2 (σ0.asModuleEquiv.symm s) := by
        rw [LinearEquiv.symm_apply_eq, modMap_apply, LinearEquiv.apply_symm_apply]
      show ρ.asModuleEquiv.symm (f s) ∈ N
      rw [hfs]
      exact (le_iSup₂ (f := fun (f : S0 →ₗ[ℂ] X) (hf : f ∈ homInto σ0 ρ C) =>
        LinearMap.range (modMap f hf.2)) f hf) ⟨_, rfl⟩
    exact hle hv1
  let w : N := ⟨_, hvN⟩
  have hw : w ≠ 0 := fun h => hv0 (by
    have := congrArg (fun x : N => ρ.asModuleEquiv x.1) h
    simpa [w] using this)
  have hew : e w ≠ 0 := fun h => hw (e.map_eq_zero_iff.1 h)
  obtain ⟨i, hi⟩ : ∃ i, e w i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hew (Finsupp.ext h)
  refine killed_ne_bot (LinearEquiv.refl _ σ0.asModule) hi (fun x hx => ?_) hk
  have hxw : x • w = 0 := by
    apply Subtype.ext
    show x • ρ.asModuleEquiv.symm v = 0
    apply ρ.asModuleEquiv.injective
    rw [Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply, mem_killed.1 hv2 x hx,
      map_zero]
  have := congrArg (fun u => e u i) hxw
  simpa [map_smul, Finsupp.smul_apply] using this

end GlobalTheory.RepCount

end
