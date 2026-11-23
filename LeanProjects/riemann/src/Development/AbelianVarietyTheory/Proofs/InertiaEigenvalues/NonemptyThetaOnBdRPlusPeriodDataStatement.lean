import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_thetaOnBdRPlus_periodData : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime], Nonempty (ThetaL (D.loc l) (D.locA l)) := by
  first | exact @GlobalTheory.ThetaTie.nonempty_thetaL | exact GlobalTheory.ThetaTie.nonempty_thetaL | (intros; apply GlobalTheory.ThetaTie.nonempty_thetaL <;> assumption)
