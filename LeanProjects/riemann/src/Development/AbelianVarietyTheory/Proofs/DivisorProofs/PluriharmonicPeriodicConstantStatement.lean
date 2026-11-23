import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluriharmonicPeriodicConstant
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pluriharmonic_periodic_constant : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : V → ℝ) (K Λ : Set V), ContDiff ℝ 1 f → (∀ a : V, Differentiable ℂ (fun z => ((fderiv ℝ f z a : ℝ) : ℂ) - Complex.I * ((fderiv ℝ f z (Complex.I • a) : ℝ) : ℂ))) → IsCompact K → (∀ l ∈ Λ, ∀ z, f (z + l) = f z) → (∀ z, ∃ k ∈ K, ∃ l ∈ Λ, z = k + l) → ∀ z, f z = f 0 := by
  first | exact @GlobalTheory.periodic_const_of_holomorphic_differential | exact GlobalTheory.periodic_const_of_holomorphic_differential | (intros; apply GlobalTheory.periodic_const_of_holomorphic_differential <;> assumption)
