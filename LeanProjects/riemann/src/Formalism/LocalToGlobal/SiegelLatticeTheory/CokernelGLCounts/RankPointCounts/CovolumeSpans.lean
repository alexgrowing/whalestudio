import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem vector_eq_zero_of_orbital_zero {D : D7} {X : HidaSetting D} (Y : Full X) {u : D.what₂.Word} (t : GTu Y u)
    (h : OOt t = 0) : (Y.tO u u).vec t = 0 := by
  unfold Full.tO tOf
  dsimp only
  unfold vec ampN
  rw [h]
  simp only [map_zero, smul_zero, ite_self]
  first
    | rfl
    | simp

theorem irrVec_nohyp {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) (t : GTu Y u) (ht : ¬ t.relevant) :
    (Y.tO u u).vec t = 0 :=
  vector_eq_zero_of_orbital_zero Y t
    (Vanish.ooVanish_of Formalism.L2.SG.Closed.AvgCore_holds Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds
      Formalism.L2.SG.Closed.ChiTrivialC_holds Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds
      Formalism.L2.SG.Pf.roDiscreteC_holds Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds Y t ht)

theorem IrrVecC_holds : IrrVecC := by
  intro D X Y u _ _ t _ ht
  exact irrVec_nohyp Y u t ht

end Formalism.L2.SG.KappaOffDiagonal
