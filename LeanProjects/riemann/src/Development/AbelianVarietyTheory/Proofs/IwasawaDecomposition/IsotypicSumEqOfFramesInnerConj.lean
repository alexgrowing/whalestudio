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

namespace GlobalTheory.FrameIsot

variable {H S X : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X]

theorem iSup_le_of_intertwine (σ₁ σ₂ : Representation ℂ H S) (ρ : Representation ℂ H X) (C : Submodule ℂ X)
    (T : S →ₗ[ℂ] S) (hT : Function.Surjective T) (hc : ∀ g s, σ₁ g (T s) = T (σ₂ g s)) :
    (⨆ f ∈ homInto σ₁ ρ C, LinearMap.range f) ≤ ⨆ f ∈ homInto σ₂ ρ C, LinearMap.range f := by
  refine iSup₂_le fun f hf => ?_
  have hm : f ∘ₗ T ∈ homInto σ₂ ρ C := by
    refine ⟨fun s => hf.1 (T s), fun g s => ?_⟩
    show f (T (σ₂ g s)) = ρ g (f (T s))
    rw [← hc]; exact hf.2 g (T s)
  have hr : LinearMap.range (f ∘ₗ T) = LinearMap.range f := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.2 hT, Submodule.map_top]
  exact hr ▸ le_iSup₂_of_le (f ∘ₗ T) hm le_rfl

end GlobalTheory.FrameIsot

open GlobalTheory.FrameIsot in
theorem GlobalTheory.FrameIsot.iSup_homInto_frame_conj : ∀ {D : D7} (Y W : HSp D) {n : ℕ} (PY : principalLevelFrame.RowPsi Y n) (PW : principalLevelFrame.RowPsi W n) (Φ : GfC Y ≃ₜ* GfC W) (h : Formalism.AUTREP.GAf D.host.E n), (∀ κ, ((Φ ⟨PY.ψ κ, PY.into κ⟩ : GfC W) : GA D W) = PW.ψ (h * κ * h⁻¹)) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC W) X) (C : Submodule ℂ X) (π : Formalism.L2.NG.FinTyp D.host.E n), (⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv PY).symm.toMonoidHom) (ρ.comp Φ.toMulEquiv.toMonoidHom) C, LinearMap.range f) = ⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv PW).symm.toMonoidHom) ρ C, LinearMap.range f := by
  intro D Y W n PY PW Φ h hΦ X _ _ ρ C π
  rw [GlobalTheory.PartDims.homInto_comp]
  set eY := GlobalTheory.KapIsot.eqv PY
  set eW := GlobalTheory.KapIsot.eqv PW
  have key : ∀ κ', eY.symm (Φ.toMulEquiv.symm (eW κ')) = h⁻¹ * κ' * h := by
    intro κ'
    rw [MulEquiv.symm_apply_eq, MulEquiv.symm_apply_eq]
    apply Subtype.ext
    have := hΦ (h⁻¹ * κ' * h)
    rw [show h * (h⁻¹ * κ' * h) * h⁻¹ = κ' by group] at this
    exact this.symm
  have hW : ∀ κ', eW.symm (eW κ') = κ' := fun κ' => MulEquiv.symm_apply_apply _ _
  apply le_antisymm
  · refine iSup_le_of_intertwine _ _ ρ C (GlobalTheory.OccRowVec.finRep π h⁻¹) ?_ ?_
    · intro s; exact ⟨GlobalTheory.OccRowVec.finRep π h s, by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]⟩
    · intro g s
      obtain ⟨κ', rfl⟩ := eW.surjective g
      show GlobalTheory.OccRowVec.finRep π (eY.symm (Φ.toMulEquiv.symm (eW κ'))) _ = GlobalTheory.OccRowVec.finRep π h⁻¹ (GlobalTheory.OccRowVec.finRep π (eW.symm (eW κ')) s)
      rw [key, hW, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2; group
  · refine iSup_le_of_intertwine _ _ ρ C (GlobalTheory.OccRowVec.finRep π h) ?_ ?_
    · intro s; exact ⟨GlobalTheory.OccRowVec.finRep π h⁻¹ s, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
    · intro g s
      obtain ⟨κ', rfl⟩ := eW.surjective g
      show GlobalTheory.OccRowVec.finRep π (eW.symm (eW κ')) _ = GlobalTheory.OccRowVec.finRep π h (GlobalTheory.OccRowVec.finRep π (eY.symm (Φ.toMulEquiv.symm (eW κ'))) s)
      rw [key, hW, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2; group
