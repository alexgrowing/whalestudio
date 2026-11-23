import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluriharmonicHolomorphicDerivative
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pluriharmonic_holomorphic_derivative : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : V → ℝ), ContDiff ℝ ∞ f → (∀ z a w : V, fderiv ℝ (fun y => fderiv ℝ f y (Complex.I • a)) z w = fderiv ℝ (fun y => fderiv ℝ f y (Complex.I • w)) z a) → ∀ a : V, Differentiable ℂ (fun z => ((fderiv ℝ f z a : ℝ) : ℂ) - Complex.I * ((fderiv ℝ f z (Complex.I • a) : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.pluriharmonic_dz_differentiable | exact GlobalTheory.pluriharmonic_dz_differentiable | (intros; apply GlobalTheory.pluriharmonic_dz_differentiable <;> assumption)
