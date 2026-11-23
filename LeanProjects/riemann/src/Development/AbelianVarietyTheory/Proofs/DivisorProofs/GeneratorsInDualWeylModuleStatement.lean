import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorsInDualWeylModule
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generators_in_dual_weyl_module : ∀ (K : Type) [Field K] (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n), GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg → GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg → ∀ t : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Gen lam sg, GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.piGen K lam sg t ∈ dualWeyl K n n sg.natW ∧ ∃ G : BP K n, bmLift K n (lamN lam) (fun s => lamN lam s - sg.natW s) (GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.piGen K lam sg t) G ∧ GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.phiGen K lam sg t = incl K n G := by
  first | exact @GlobalTheory.BrCompare.LiftGen.piGen_mem_and_lift | exact GlobalTheory.BrCompare.LiftGen.piGen_mem_and_lift | (intros; apply GlobalTheory.BrCompare.LiftGen.piGen_mem_and_lift <;> assumption)
