import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsOfAllPartProperties
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseLevelRowsEqDimensionStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.Ind
theorem pRows_of_parts_alt : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.FiringPointSummands D O c b → _root_.GlobalTheory.Fc.Ind.summandRealBound D O c b →
    _root_.GlobalTheory.Fc.Ind.summandPrimitive D O c b → _root_.GlobalTheory.Fc.Ind.FramePointSummands D O c b → _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b → _root_.GlobalTheory.Fc.Ind.NormJumpPointSummands D O c b → Formalism.BasicNotions.GoodFTAll D → b.pt.CompatibilityConditions →
    _root_.GlobalTheory.Fc.Ind.RowPointSummands D O c b := by
  intro D O c b hF hB hP hFr hD hN hG hT
  exact
    { exAt := hF.1
      jEvBar := hF.2.1
      geoAct := hF.2.2.1
      evInj := hF.2.2.2
      ioExt := hB.ioExt
      oneMap := hB.oneMap
      prim := hP.1
      sep := hP.2
      ok := b.ok1
      framesOK := b.B.Q.frames hFr
      divRows := hD
      psi := b.psi
      d0 := _root_.GlobalTheory.T.ind_piece_degree_zero D O c b
      export_ := hN
      goodFT := hG
      w1 := fun w hw => ((b.muDef 0 0).2.2.2 w).2 hw
      ties := hT }
end GlobalTheory.Fc.Ind
end
