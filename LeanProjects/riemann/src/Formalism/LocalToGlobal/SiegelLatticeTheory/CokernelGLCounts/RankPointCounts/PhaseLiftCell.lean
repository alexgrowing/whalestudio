import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FinitePhase
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting

noncomputable section

namespace Formalism.L2.SG.Pf.PhaseLiftCell

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem realLink' {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') what₂ rows') (v : InfinitePlace X.B.I.F) :
    Formalism.L2.SG.RealObj.ZhatO (Formalism.L2.SG.RealObj.ZX X u u' 1 s.pt.1 v) =
      (ZhatOM (ZhatL (lf D (X.Fu u)) s.frame)).map (fun x => X.B.I.φ v (X.ιE.symm x)) := by
  obtain ⟨M, _, hM1, _, hM3⟩ := s.rep.2.1
  have hiso : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hfam : ∀ (w : D.what₂.Word) (a : Fin (D.R.rS + 1)),
      Formalism.L2.SG.RealObj.fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) a =
        rv X.B.I v (X.crd ((X.Fu w).fvec a)) := by
    intro w a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp [Formalism.L2.SG.RealObj.fam, FlagG.fvec, X.flagZVector w, HidaSetting.zR]
    · simp [Formalism.L2.SG.RealObj.fam, FlagG.fvec, X.Fu_e w, HidaSetting.eR]
  ext a b
  simp only [Formalism.L2.SG.RealObj.ZhatO, ZhatOM, Formalism.L2.SG.RealObj.ZX, Formalism.L2.SG.RealObj.Zhat,
    Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc, Matrix.map_apply, Complex.ofReal_one, one_pow, inv_one,
    one_smul]
  rw [hfam u a, hfam u' b]
  have h1 : Formalism.MainNotions.S.uMat (s.pt.1 v) = (X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
      X.B.I.P v := hM1 v
  rw [h1, Formalism.L2.SG.Pf.Level.rv_mulVec, ← hM3, Formalism.L2.SG.PoincareInHH.Cut.hJ_crd]
  have h2 : ZhatL (lf D (X.Fu u)) s.frame a b = (VS D).hT ((X.Fu u).fvec a) (s.lin ((X.Fu u').fvec b)) := by
    rw [← Formalism.L2.SG.Pf.Act.frame_mapLF hiso (X.Fu u') b]
    rfl
  rw [h2, map_mul, map_mul]
  simp only [map_pow, map_neg, map_one]
  rw [X.φ_eq, RingEquiv.apply_symm_apply]
  rfl

theorem liftCell_of_atSome {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (h1 : Formalism.L2.SG.Pf.RowForm.LiftAtSomeC X Y u u' κ) : Formalism.L2.SG.Pf.FinitePhase.LiftCellC X Y u u' κ := by
  intro R ρ s hrel
  obtain ⟨w0, hw0⟩ := h1 R ρ s hrel
  have hat : s.1.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) :=
    Formalism.L2.SG.PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  have hcell := ((Formalism.L2.SG.TermDef.atPt_mk (Formalism.L2.SG.Pf.g_value_function _ _ _) (Formalism.L2.SG.Pf.cell_function_holds _ _ _)
    ⟨s.1.frame, s.1.rep.2.2.2.2⟩ _).1 hat).2
  obtain ⟨L, U, hL, hU, hLU⟩ := hcell
  refine ⟨L, U, hL, hU, hLU, fun v => ?_⟩
  rw [realLink' X u u' s.1 v]
  exact congrArg (fun Z => Z.map (fun x => X.B.I.φ v (X.ιE.symm x))) hLU

theorem phaseAgreement_of_lift {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (h1 : Formalism.L2.SG.Pf.RowForm.LiftAtSomeC X Y u u' κ) (hF : Formalism.L2.SG.Pf.FinitePhase.FinPhaseC X Y u u' κ) :
    Formalism.L2.SG.Pf.RowForm.PhaseTieC X Y u u' κ :=
  Formalism.L2.SG.Pf.FinitePhase.phaseTieC_of X Y u u' κ (liftCell_of_atSome X Y u u' κ h1) hF

end Formalism.L2.SG.Pf.PhaseLiftCell
