import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianClassNumberItemsAllRanks
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianClassNumberItems_all_ranks : ∀ (D : D7) (n : ℕ), ClassItemsAt D n := by
  first | exact @GlobalTheory.classItemsAt_all | exact GlobalTheory.classItemsAt_all | (intros; apply GlobalTheory.classItemsAt_all <;> assumption)
