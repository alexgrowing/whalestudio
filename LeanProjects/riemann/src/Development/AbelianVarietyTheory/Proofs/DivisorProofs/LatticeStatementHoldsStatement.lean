import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStatementHolds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_statement_holds : LatSt := by
  first | exact @GlobalTheory.FlatModel.LatDual.latSt | exact GlobalTheory.FlatModel.LatDual.latSt | (intros; apply GlobalTheory.FlatModel.LatDual.latSt <;> assumption)
