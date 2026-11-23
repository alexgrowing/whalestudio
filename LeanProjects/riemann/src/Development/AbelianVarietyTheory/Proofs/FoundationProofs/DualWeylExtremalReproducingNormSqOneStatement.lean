import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualWeylExtremalReproducingNormSqOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
open GlobalTheory.DualWeyl MvPolynomial NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_extremal_reproducing_normSq_one : ∀ (N : ℕ) (la : Fin N → ℕ), Antitone la → (∀ f ∈ nabla la ℂ, form la f (extremal la ℂ) = evalAt 1 f) ∧ normSq la (extremal la ℂ) = 1 := by
  first | exact @GlobalTheory.DualWeyl.Repro.extremal_reproducing | exact GlobalTheory.DualWeyl.Repro.extremal_reproducing | (intros; apply GlobalTheory.DualWeyl.Repro.extremal_reproducing <;> assumption)
