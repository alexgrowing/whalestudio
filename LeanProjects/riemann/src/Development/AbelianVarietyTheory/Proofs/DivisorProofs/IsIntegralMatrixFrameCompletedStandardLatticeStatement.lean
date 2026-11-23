import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixFrameCompletedStandardLattice
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralMatrix_frame_completedStandardLattice : ∀ {D : D7} {n : ℕ} (β : GL (Fin n) (EAf D)), Formalism.L2.DIV.IsFrame β (stdL D n) → IsIntM β.val ∧ IsIntM (β⁻¹).val := by
  first | exact @GlobalTheory.StdRead.isIntM_of_isFrame_stdL | exact GlobalTheory.StdRead.isIntM_of_isFrame_stdL | (intros; apply GlobalTheory.StdRead.isIntM_of_isFrame_stdL <;> assumption)
