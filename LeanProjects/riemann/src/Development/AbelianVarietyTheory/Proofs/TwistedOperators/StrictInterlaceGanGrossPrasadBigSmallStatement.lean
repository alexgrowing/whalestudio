import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StrictInterlaceGanGrossPrasadBigSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictInterlace_ganGrossPrasad_big_small : ∀ (S : Sizes) (Q : Entries S), Q.Good → GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.Interlace Q.bigPar Q.smallPar := by
  first | exact @GlobalTheory.StrictInterlace.interlace_big_small | exact GlobalTheory.StrictInterlace.interlace_big_small | (intros; apply GlobalTheory.StrictInterlace.interlace_big_small <;> assumption)
