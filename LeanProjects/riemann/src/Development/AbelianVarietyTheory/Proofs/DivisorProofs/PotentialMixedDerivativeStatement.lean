import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialMixedDerivative
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potential_mixed_derivative : ∀ {g : ℕ} (ψ : (Fin g → ℂ) → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (Ω : (Fin g → ℂ) → (Fin g → ℂ) → ℝ) (z : Fin g → ℂ)
    (hΩ : ∀ v w, fderiv ℝ (fun z' => fderiv ℝ ψ z' (Complex.I • w)) z v -
      fderiv ℝ (fun z' => fderiv ℝ ψ z' (Complex.I • v)) z w = 4 * π * Ω v w)
    (a c : Fin g),
    d10 (fun z' => d01 (fun z'' => (ψ z'' : ℂ)) z' (ev c)) z (ev a) =
      -(π : ℂ) * Ω (ev a) (Complex.I • ev c) + (π : ℂ) * Complex.I * Ω (ev a) (ev c) := by
  first | exact @GlobalTheory.TorsionForm.FlatAcyc.dd_real_hessian | exact GlobalTheory.TorsionForm.FlatAcyc.dd_real_hessian | (intros; apply GlobalTheory.TorsionForm.FlatAcyc.dd_real_hessian <;> assumption)
