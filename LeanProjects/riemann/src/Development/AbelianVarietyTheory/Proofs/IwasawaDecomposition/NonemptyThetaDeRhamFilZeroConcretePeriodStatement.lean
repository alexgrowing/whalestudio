import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriod
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_theta_deRhamFil_zero_concretePeriod : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → Nonempty (Formalism.MainNotions.LocalSituation.ThetaL P AI) := by
  first | exact @GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL | exact GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL | (intros; apply GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL <;> assumption)
