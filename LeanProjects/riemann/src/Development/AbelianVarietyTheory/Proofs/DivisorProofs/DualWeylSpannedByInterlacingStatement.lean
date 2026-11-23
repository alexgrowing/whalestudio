import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylSpannedByInterlacing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_weyl_spanned_by_interlacing : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n), GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg → GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg → dualWeyl K n n sg.natW ≤ Submodule.span K (Set.range (GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.piGen K lam sg)) := by
  first | exact @GlobalTheory.BrCompare.Surj.dualWeyl_le_span_piGen | exact GlobalTheory.BrCompare.Surj.dualWeyl_le_span_piGen | (intros; apply GlobalTheory.BrCompare.Surj.dualWeyl_le_span_piGen <;> assumption)
