import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOTargetSliceOrthogonalSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunO_target_slice_orthogonal_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (f : WO T S → ℂ) (y : WO T L), IsThetaFunO ψ T S f → IsThetaFunO ψ T A (fun w => f ((o.resT T).symm (w, y))) := by
  first | exact @GlobalTheory.FinPl.ExtZero.isThetaFunO_sliceT | exact GlobalTheory.FinPl.ExtZero.isThetaFunO_sliceT | (intros; apply GlobalTheory.FinPl.ExtZero.isThetaFunO_sliceT <;> assumption)
