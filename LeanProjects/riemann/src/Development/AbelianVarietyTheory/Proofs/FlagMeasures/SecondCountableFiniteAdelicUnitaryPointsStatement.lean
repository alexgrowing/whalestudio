import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SecondCountableFiniteAdelicUnitaryPoints
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondCountable_finiteAdelicUnitaryPoints : ∀ (I : AutInst), SecondCountableTopology I.Gf := by
  first | exact @GlobalTheory.CongTop.secondCountable_finiteAdelicPoints | exact GlobalTheory.CongTop.secondCountable_finiteAdelicPoints | (intros; apply GlobalTheory.CongTop.secondCountable_finiteAdelicPoints <;> assumption)
