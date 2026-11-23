import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJoint
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.JointPf

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def OOQuot (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) → ∀ y : ∀ v, X.Vloc u' v,
      (haveI := FiniteDimensional.complete ℂ (X.Vpi u);
        Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
          (X.tensU u' y) =
      X.tensU u (fun v => (haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
        Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v)) (y v))

def PlaceJ (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' →
    ∀ (v : InfinitePlace X.B.I.F) (y : X.Vloc u' v),
      X.piLoc u v (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u v) v h⁻¹)
        ((haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
          Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v))
          (X.piLoc u' v (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u' v) v h') y)) =
      P.eP v
        (((((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (P.S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
            (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
          Formalism.FourierDecayAlt.D.vecV (P.T (P.τ.symm v)).base (P.ν' (P.τ.symm v)) (P.m₀ (P.τ.symm v)) (P.f (P.τ.symm v))
            (Formalism.FourierDecayAlt.D.toStd P.S.G.r P.S.g 1 (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p)))
          ((P.eQ v).symm y))

theorem jointTensor_of_steps (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hQ : OOQuot X u u' νq νl) (hP : PlaceJ P sc i0 i0' νl) : P.JointTensor sc i0 i0' νq := by
  unfold Formalism.L2.SG.Pf.Carrier.Parts.JointTensor
  intro p w hpw hγ hG h h' hF x
  rw [X.tensU_equiv, hQ w hγ hG, X.tensU_equiv]
  · exact congrArg (fun f => X.tensU u f) (funext fun v => hP p w hpw hγ hG h h' hF v (x v))
  all_goals
    first
    | exact hF.2.1
    | (intro v y hy
       have h1 := hF.1 v y hy
       nth_rewrite 1 [← h1]
       rw [Matrix.mulVec_mulVec, Pi.inv_apply]
       simp only [uMat]
       rw [← Units.val_mul, ← MulMemClass.coe_mul, inv_mul_cancel, OneMemClass.coe_one, Units.val_one,
         Matrix.one_mulVec])

end Formalism.L2.SG.Pf.Carrier.JointPf
