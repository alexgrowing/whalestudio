import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeStabiliserIsCompactIsOpen
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLatticeStabiliser_isCompact_isOpen : ∀ (I : AutInst), IsCompact I.Kset ∧ IsOpen I.Kset ∧ LocallyCompactSpace I.Gf ∧ T2Space I.Gf := by
  first | exact @GlobalTheory.adelicStab_isCompact_isOpen | exact GlobalTheory.adelicStab_isCompact_isOpen | (intros; apply GlobalTheory.adelicStab_isCompact_isOpen <;> assumption)
