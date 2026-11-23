import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FinitePhaseSimp
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormRepX

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.LiftedPhaseAgreement

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

theorem liftAtSomeC_holds : Formalism.L2.SG.Pf.RowForm.LiftAtSomeC X Y u u' κ := by
  intro R ρ s hs
  have hA := Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u' s.1.toTerm
  have hG : s.1.toTerm.G ≠ 0 := by
    intro h
    apply s.2.1
    show Formalism.L2.SG.TermOp.Gt s.1 = 0
    simp [Formalism.L2.SG.TermOp.Gt, Formalism.L2.SG.TermOp.GTerm.G, h]
  exact hA hG hs

theorem phaseTieC_holds (hP : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) :
    Formalism.L2.SG.Pf.RowForm.PhaseTieC X Y u u' κ :=
  Formalism.L2.SG.Pf.PhaseLiftCell.phaseAgreement_of_lift X Y u u' κ (liftAtSomeC_holds X Y u u' κ)
    (Formalism.L2.SG.Pf.FinitePhaseConjugation.finPhaseC_of (hNR := Formalism.L2.SG.Pf.normRepExists_of
      (Formalism.L2.SG.Pf.NormRepX.norm_representative_holds D u u' hP) (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u))
      (h1 := liftAtSomeC_holds X Y u u' κ))

end Formalism.L2.SG.Pf.LiftedPhaseAgreement
