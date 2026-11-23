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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicities
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelsMultiplicityEqual
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.IsoRankMult

open GlobalTheory.RepCount in
theorem iso_of_hom_into_sum : ∀ (H S0 S X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X) (C : Submodule ℂ X), σ0.IsIrreducible → σ.IsIrreducible → ∀ f ∈ homInto σ ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g), f ≠ 0 → Nonempty (σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) := by
  intro H S0 S X _ _ _ _ _ _ _ σ0 σ ρ C h0 h1 f hf hne
  let R := MonoidAlgebra ℂ H
  haveI : IsSimpleModule R σ0.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ0).mp h0
  haveI : IsSimpleModule R σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp h1

  let N' : Submodule R ρ.asModule :=
    ⨆ (g : S0 →ₗ[ℂ] X) (hg : g ∈ homInto σ0 ρ C), LinearMap.range (modMap g hg.2)
  have hN'iso : N' ≤ isotypicComponent R ρ.asModule σ0.asModule := by
    refine iSup₂_le fun g hg => ?_
    rcases LinearMap.injective_or_eq_zero (modMap (σ := σ0) (ρ := ρ) g hg.2) with hi | hz
    · exact le_sSup ⟨(LinearEquiv.ofInjective _ hi).symm⟩
    · rw [hz, LinearMap.range_zero]; exact bot_le
  have hsub : (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) ≤
      (N'.restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨s, rfl⟩
    have hmem : modMap (σ := σ0) (ρ := ρ) g hg.2 (σ0.asModuleEquiv.symm s) ∈ N' :=
      (le_iSup₂_of_le (f := fun (g : S0 →ₗ[ℂ] X) (hg : g ∈ homInto σ0 ρ C) =>
        LinearMap.range (modMap (σ := σ0) (ρ := ρ) g hg.2)) g hg le_rfl) ⟨_, rfl⟩
    show ρ.asModuleEquiv.symm (g s) ∈ N'
    convert hmem using 1
    apply ρ.asModuleEquiv.injective
    rw [modMap_apply]; simp
  let F := modMap (σ := σ) (ρ := ρ) f hf.2
  have hFi : Function.Injective F := by
    rcases LinearMap.injective_or_eq_zero F with hi | hz
    · exact hi
    · exfalso; apply hne
      ext s
      have := congrArg (fun φ => ρ.asModuleEquiv (φ (σ.asModuleEquiv.symm s))) hz
      simp only [F, modMap_apply, LinearMap.zero_apply, map_zero] at this
      simpa using this
  have hle : LinearMap.range F ≤ isotypicComponent R ρ.asModule σ0.asModule := by
    refine le_trans ?_ hN'iso
    rintro _ ⟨x, rfl⟩
    have hx := hsub (hf.1 (σ.asModuleEquiv x))
    have : ρ.asModuleEquiv.symm (f (σ.asModuleEquiv x)) = F x := by
      apply ρ.asModuleEquiv.injective; simp [F, modMap_apply]
    rw [← this]; exact hx
  let e := LinearEquiv.ofInjective F hFi
  haveI : IsSimpleModule R (LinearMap.range F) := IsSimpleModule.congr e.symm
  obtain ⟨e'⟩ := isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent R ρ.asModule σ0.asModule) (LinearMap.range F) hle
  exact ⟨e.trans e'⟩

end GlobalTheory.IsoRankMult
