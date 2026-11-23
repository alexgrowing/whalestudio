import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylModuleLeSpanExtremalTranslates
import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualWeylModuleSimpleCharZeroStatement
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylModule_le_span_extremalTranslates : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : DomWeight n), nablaSq K n lam ≤ Submodule.span K (Set.range fun g : GL (Fin n) K => sqAct K n lam g (extremal K n lam)) := by
  first | exact @GlobalTheory.nablaSq_le_span_extremal | exact GlobalTheory.nablaSq_le_span_extremal | (intros; apply GlobalTheory.nablaSq_le_span_extremal <;> assumption)
