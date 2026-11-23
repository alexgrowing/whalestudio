import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigCellPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustGPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FrameMeasStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfT
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.EtaStatementHolds

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bigCellStatement_holds : BigCellStatement (E := E) := bigCell_of (lu_holds (E := E))

theorem kaUnfoldStatement_holds : KaUnfoldStatement (E := E) :=
  kaUnfold_of (measInv_holds (E := E)) SumBoundStatement_holds

theorem pairUnfoldStatement_holds : PairUnfoldStatement (E := E) :=
  PairUnfoldPf.pairUnfold_of (measInv_holds (E := E)) kaUnfoldStatement_holds (lu_holds (E := E))

theorem extFStatement_holds : ExtFStatement (E := E) :=
  extF_of (lu_holds (E := E)) (FrameMeasStatement_holds (E := E))

theorem onto_of_poin_extF (hPoin : PoinStatement (E := E)) (hExtF : ExtFStatement (E := E)) :
    OntoStatement (E := E) :=
  onto_of hPoin hExtF (RGF.rhGradF_holds (E := E)) (exhaustG_holds (E := E)) kaUnfoldStatement_holds
    pairUnfoldStatement_holds bigCellStatement_holds (OFC.omFConn_of_cm (E := E))

theorem kronHolPsiStatement_holds : KronHolPsiStatement (E := E) :=
  kronHolPsi_of_frameMeas (FrameMeasStatement_holds (E := E))

theorem interp_of_poin (hP : PoinStatement (E := E)) : InterpStatement (E := E) :=
  interp_of hP kronHolPsiStatement_holds

theorem interpC_of_poin (hP : PoinStatement (E := E))
    (hη : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X), ∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 →
      ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ +
          leviO X x0 (fun x => (1 + Xa.c1 / Xa.a1) * Xa.ps0 x) z ξ) :
    InterpCStatement (E := E) := interpC_of hP kronHolPsiStatement_holds hη

theorem ontoStatement_holds : OntoStatement (E := E) :=
  onto_of_poin_extF (poin_holds (E := E)) extFStatement_holds

theorem interpStatement_holds : InterpStatement (E := E) := interp_of_poin (poin_holds (E := E))

theorem interpC_of_eta (hη : EtaStatement (E := E)) : InterpCStatement (E := E) :=
  interpC_of_poin (poin_holds (E := E)) hη

theorem interpCStatement_holds : InterpCStatement (E := E) := interpC_of_eta (EtaPf.eta_holds (E := E))

end ReciprocityTheory.ChartRestriction.G.AR.Up
