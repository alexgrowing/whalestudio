import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramCPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AmpIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActMassC
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActLFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RightActionThreeFamilies
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsColLatRepS
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormChiNBi

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.NormCut

theorem colFreeAll (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word) :
    ColFree (X.Fu u) Y.TR (Y.cs u) (Aset Y.TR (Y.cs u)) (scOf Y.TR (Y.cs u)) :=
  colFree_steps Y.TR (Y.cs u) Y.hK (Y.colReps u) (Formalism.L2.SG.Closed.NeatKu_holds X u Y.hK)
    (Formalism.L2.SG.Pf.NormSteps.levi_onto_reduction Y.TR (Y.cs u))
    (Formalism.L2.SG.Pf.NormSteps.column_lattice_representatives (Y.cs u) Y.hK (Y.rowsOK u)) (Formalism.L2.SG.Pf.massAC_holds D X Y u)

theorem leftActC'_of_PD (hPD : ∀ D : D7, Formalism.L2.SG.Saturated.PDIso D) : Formalism.L2.SG.Pf.SatGramActL.LeftActC' := by
  have hB : Formalism.L2.SG.Pf.SatGramActL.ChiNBiAll := by
    first
    | exact fun D X => chi_n_bilinear X
    | (intro D X; exact chi_n_bilinear X)
  have hGen : ∀ D : D7, Formalism.L2.SG.Saturated.GenIso (VS D) D.R.rS (gS D) := by
    intro D
    first
    | exact Formalism.L2.SG.Pf.generic_isomorphism_holds (gS D)
    | exact Formalism.L2.SG.Pf.generic_isomorphism_holds _
    | exact Formalism.L2.SG.Pf.generic_isomorphism_holds _ _ _
  exact Formalism.L2.SG.Pf.SatGramActL.left_action_of_local_data hPD hGen Formalism.L2.SG.Pf.iotaRepC_holds
    Formalism.L2.SG.Pf.ampRepNC_holds hB

theorem rightActC'_holds : Formalism.L2.SG.Pf.SatGramActR.RightActC' := by
  have hB : Formalism.L2.SG.Pf.SatGramActL.ChiNBiAll := by
    first
    | exact fun D X => chi_n_bilinear X
    | (intro D X; exact chi_n_bilinear X)
  exact Formalism.L2.SG.Pf.SatGramActR.right_action_three_families hB Formalism.L2.SG.Pf.iotaRepC_holds Formalism.L2.SG.Pf.ampRepNC_holds

theorem normExpSatC'_of_PD (hPD : ∀ D : D7, Formalism.L2.SG.Saturated.PDIso D) : NormExpSatC' := by
  have hN : NeatC := Formalism.L2.SG.Closed.NeatC_holds
  exact normExpSatC'_of_acts hN Formalism.L2.SG.Pf.massAC_holds (leftActC'_of_PD hPD) rightActC'_holds

theorem degLeftAct_of_PD (hPD : ∀ D : D7, Formalism.L2.SG.Saturated.PDIso D) (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (Y : Full X) (u : D.what₂.Word) (h1 : OOIntAll X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u))
    (h2 : AmpWellDef (X.Fu u) (X.Fu u) (Y.cs u) (Y.cs u)) (h3 : OOFundIndep X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)) :
    Formalism.L2.SG.Pf.SatGram.LeftAct (X.Fu u) (X.Fu u) Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) (Y.tO u u).degSet
      (Aset Y.TR (Y.cs u)) :=
  leftActC'_of_PD hPD D X Y u u h1 h2 h3 _ (by simp)

theorem degRightAct_holds (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word)
    (h1 : OOIntAll X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u))
    (h2 : AmpWellDef (X.Fu u) (X.Fu u) (Y.cs u) (Y.cs u)) (h3 : OOFundIndep X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)) :
    Formalism.L2.SG.Pf.SatGram.RightAct (X.Fu u) (X.Fu u) Y.TR (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) (Y.tO u u).degSet
      (Aset Y.TR (Y.cs u)) :=
  rightActC'_holds D X Y u u h1 h2 h3 _ (by simp)

end Formalism.L2.SG.NormCut
