import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJoint
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DFrameAtPfB

noncomputable section

open NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.PtRepPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace DFrameAtPf

theorem matW_liftU {n k : ℕ} {ε : Fin n → Bool} (wb : Fin k → Fin n → ℂ)
    (hon : ∀ i j, hJ ε (wb i) (wb j) = if i = j then 1 else 0)
    (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    (Matrix.of fun a b => hJ ε (wb a) (uMat (liftU wb hon U hU) *ᵥ wb b)) = U := by
  ext a b
  rw [Matrix.of_apply, liftU_mulVec]
  have h1 := congrFun (wCoord_liftM hon U (wb b)) a
  have h2 : wCoord ε wb (wb b) = Pi.single b 1 := by
    funext i
    show hJ ε (wb i) (wb b) = _
    rw [hon, Pi.single_apply]
  rw [h2, mulVec_single_one] at h1
  exact h1

end DFrameAtPf

open DFrameAtPf

variable {D : D7}

theorem dFrame_any (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (s0 sc : ℝ) (hsc : sc ≠ 0)
    (i0 : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (γ : X.B.I.Ginf) (hG : ∀ v, 0 < GX X u u' s0 γ v) :
    ∃ h h', IsDFrameX X u u' sc i0 i0 γ h h' := by
  have hloc : ∀ v, ∃ h h' : Matrix (Fin D.R.k) (Fin D.R.k) ℂ,
      IsDFrame (X.B.I.ε v) (frm X u sc v) (frm X u' sc v) (uMat (γ v)) (uMat ((γ v)⁻¹)) (X.wfr u v)
        (X.wfr u' v) (i0 v) (i0 v) h h' := fun v =>
    dframe_loc (frU X u v) (frU X u' v) rfl (i0 v) (γ v) sc hsc
      (gv_pos_scale (Tw u) (Tw u') (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u'))
        (uMat (γ v)) s0 sc hsc (hG v))
  choose H H' hH using hloc
  have hon : ∀ uu v, ∀ i j, hJ (X.B.I.ε v) (X.wfr uu v i) (X.wfr uu v j) = if i = j then 1 else 0 :=
    fun uu v => X.wfr_on uu v
  have hmem : ∀ uu (U : ∀ v, Matrix (Fin D.R.k) (Fin D.R.k) ℂ) (hU : ∀ v, U v ∈ Matrix.unitaryGroup _ ℂ),
      (fun v => liftU (X.wfr uu v) (hon uu v) (U v) (hU v) : X.B.I.Ginf) ∈ HsetU X uu := by
    intro uu U hU v x hx
    show uMat (liftU (X.wfr uu v) (hon uu v) (U v) (hU v)) *ᵥ rv X.B.I v x = rv X.B.I v x
    rw [liftU_mulVec]
    refine liftM_fix _ _ fun i => ?_
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hx
    · exact (frU X uu v).we i a
    · exact (frU X uu v).wf i a
    · rw [Set.mem_singleton_iff] at hx; subst hx; exact (frU X uu v).wz i
  have hmat : ∀ uu (U : ∀ v, Matrix (Fin D.R.k) (Fin D.R.k) ℂ) (hU : ∀ v, U v ∈ Matrix.unitaryGroup _ ℂ) v,
      Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr uu v) v (fun v => liftU (X.wfr uu v) (hon uu v) (U v) (hU v)) = U v :=
    fun uu U hU v => matW_liftU (X.wfr uu v) (hon uu v) (U v) (hU v)
  refine ⟨fun v => liftU (X.wfr u v) (hon u v) (H v) (hH v).1,
    fun v => liftU (X.wfr u' v) (hon u' v) (H' v) (hH v).2.1,
    hmem u H (fun v => (hH v).1), hmem u' H' (fun v => (hH v).2.1), fun v => ?_⟩
  rw [hmat u H (fun v => (hH v).1) v, hmat u' H' (fun v => (hH v).2.1) v]
  exact hH v

theorem dual_frame_at_places (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ)
    (i0 : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) : DFrameAt X u u' sc i0 i0 := by
  intro hsc w _ hG
  exact dFrame_any X u u' D.host.rdE sc hsc.ne' i0 (gamW X u u' w) hG

end Formalism.L2.SG.Pf.Carrier
