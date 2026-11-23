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

namespace GlobalTheory.MultIso

variable {H S0 S X : Type} [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S]
  [AddCommGroup X] [Module ℂ X]

def precomp (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X) (B : Submodule ℂ X)
    (φ : S →ₗ[ℂ] S0) (hφ : ∀ g s, φ (σ g s) = σ0 g (φ s)) : homInto σ0 ρ B →ₗ[ℂ] homInto σ ρ B where
  toFun T := ⟨T.1 ∘ₗ φ, fun s => T.2.1 (φ s), fun g s => by
    show T.1 (φ (σ g s)) = ρ g (T.1 (φ s))
    rw [hφ]; exact T.2.2 g (φ s)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rank_homInto_of_asModule (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X)
    (B : Submodule ℂ X) (e : σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) :
    Module.rank ℂ (homInto σ ρ B) = Module.rank ℂ (homInto σ0 ρ B) := by
  let φ : S →ₗ[ℂ] S0 :=
    { toFun := fun s => σ0.asModuleEquiv (e (σ.asModuleEquiv.symm s))
      map_add' := fun a b => by simp
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        rw [show e (c • σ.asModuleEquiv.symm a) = c • e (σ.asModuleEquiv.symm a) from
          LinearMap.map_smul_of_tower e.toLinearMap c _, map_smul] }
  let ψ : S0 →ₗ[ℂ] S :=
    { toFun := fun s => σ.asModuleEquiv (e.symm (σ0.asModuleEquiv.symm s))
      map_add' := fun a b => by simp
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        rw [show e.symm (c • σ0.asModuleEquiv.symm a) = c • e.symm (σ0.asModuleEquiv.symm a) from
          LinearMap.map_smul_of_tower e.symm.toLinearMap c _, map_smul] }
  have hφψ : ∀ s, φ (ψ s) = s := fun s => by simp [φ, ψ]
  have hψφ : ∀ s, ψ (φ s) = s := fun s => by simp [φ, ψ]
  have φeq : ∀ g s, φ (σ g s) = σ0 g (φ s) := fun g s => by
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]
  have ψeq : ∀ g s, ψ (σ0 g s) = σ g (ψ s) := fun g s => by
    simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]
  let E : homInto σ0 ρ B ≃ₗ[ℂ] homInto σ ρ B :=
    { precomp σ0 σ ρ B φ φeq with
      invFun := precomp σ σ0 ρ B ψ ψeq
      left_inv := fun T => Subtype.ext (LinearMap.ext fun s => by
        show T.1 (φ (ψ s)) = T.1 s
        rw [hφψ])
      right_inv := fun T => Subtype.ext (LinearMap.ext fun s => by
        show T.1 (ψ (φ s)) = T.1 s
        rw [hψφ]) }
  exact E.rank_eq.symm

theorem homInto_iSup_range (σ0 : Representation ℂ H S0) (ρ : Representation ℂ H X) (C : Submodule ℂ X) :
    homInto σ0 ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) = homInto σ0 ρ C := by
  have hle : (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) ≤ C := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨s, rfl⟩
    exact hg.1 s
  ext f
  refine ⟨fun hf => ⟨fun s => hle (hf.1 s), hf.2⟩, fun hf => ⟨fun s => ?_, hf.2⟩⟩
  exact (le_iSup₂_of_le f hf le_rfl : LinearMap.range f ≤ ⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) ⟨s, rfl⟩

theorem rank_homInto_iSup_range : ∀ (H S0 S X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S]
    [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X)
    (C : Submodule ℂ X), Nonempty (σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) →
    Module.rank ℂ (homInto σ ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g)) = Module.rank ℂ (homInto σ0 ρ C) := by
  intro H S0 S X _ _ _ _ _ _ _ σ0 σ ρ C ⟨e⟩
  rw [rank_homInto_of_asModule σ0 σ ρ _ e, homInto_iSup_range]

end GlobalTheory.MultIso
