import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgClosed_tiltField_and_valuationRing : ∀ (l : ℕ) [Fact l.Prime], IsAlgClosed (Cb l) ∧ ValuationRing (OCb l) := by
  first | exact @GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing | exact GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing | (intros; apply GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing <;> assumption)
