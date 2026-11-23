import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJoint

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.DataInst

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

theorem signFlip_involutive {K : Type} [Ring K] (r : ℕ) : ∀ (b : ℕ) (x : Formalism.FourierDecayAlt.TB.Pt K),
    signAux r b (signAux r b x) = x
  | _, [] => rfl
  | b, (s, t) :: rest => by
    simp only [signAux, signFlip_involutive r (b + s) rest, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

variable {D : D7}

theorem exists_pt (w : Point D.host.E (D.R.rS + 1)) :
    ∃ p : Formalism.FourierDecayAlt.TB.Pt D.host.E, ptOfL (D := D) (D.R.rS + 1) p = some w := by
  set y := Formalism.L2.S.ptEquiv D.host.E (D.R.rS + 1) w with hy
  have hinv : Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.SG.DataInst.signPt D.R.rS y.1) = y.1 :=
    signFlip_involutive _ _ _
  refine ⟨Formalism.L2.SG.DataInst.signPt D.R.rS y.1, ?_⟩
  have hcond : Formalism.L2.S.IsPtL
      (Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.SG.DataInst.signPt D.R.rS y.1)) (D.R.rS + 1) := by
    rw [hinv]
    exact y.2
  unfold ptOfL Formalism.L2.SG.DataInst.ptOfList
  rw [dif_pos hcond]
  congr 1
  apply (Formalism.L2.S.ptEquiv D.host.E (D.R.rS + 1)).symm_apply_eq.mpr
  exact Subtype.ext hinv

variable (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)

def VIndepAt (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h₁ h₁' h₂ h₂', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h₁ h₁' →
      IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h₂ h₂' →
      (X.piU u h₁⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w)).comp
          (X.piU u' h₁')) =
        (X.piU u h₂⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w)).comp
          (X.piU u' h₂'))

theorem vIndepAt_of {X} {u u'} (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hJT : P.JointTensor sc i0 i0' νq) : VIndepAt X u u' sc i0 i0' νq := by
  intro w hw hG h₁ h₁' h₂ h₂' hd₁ hd₂
  obtain ⟨p, hp⟩ := exists_pt (D := D) w
  apply ContinuousLinearMap.coe_injective
  refine LinearMap.ext_on_range (X.tensU_span u') fun x => ?_
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  rw [hJT p w hp hw hG h₁ h₁' hd₁ x, hJT p w hp hw hG h₂ h₂' hd₂ x]

end Formalism.L2.SG.Pf.Carrier
