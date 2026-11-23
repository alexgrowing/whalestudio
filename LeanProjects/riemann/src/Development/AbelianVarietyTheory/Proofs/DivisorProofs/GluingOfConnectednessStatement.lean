import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluingOfConnectedness
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluing_of_connectedness : ConnSt → GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZ → GlueSt := by
  first | exact @GlobalTheory.FlatModel.glueSt_of | exact GlobalTheory.FlatModel.glueSt_of | (intros; apply GlobalTheory.FlatModel.glueSt_of <;> assumption)
